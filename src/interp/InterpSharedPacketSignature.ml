(** Staged empty mutable-interface admission. This checks the original A tree;
    it neither consumes permissions nor certifies a continuation's effects or
    bindings. The returned witness retains the exact original owner. *)
open Types
open Values
open Contexts

type slot = { path : string list; level : int; role : string; ty : ty }
type certificate = { owner : abs; slots : slot list }

let enabled () =
  Sys.getenv_opt "AENEAS_EXPERIMENTAL_SHARED_PACKET_SIGNATURE" = Some "1"

let reject span message =
  [%craise] span ("Shared packet signature: " ^ message)

let require span condition message = if not condition then reject span message

(** A-only routing: an ELet or an ordinary empty-history wrapper is not a
    reason to replace the established registration path. *)
let needs_explicit_signature (owner : abs) =
  let needed = ref false in
  let visitor = object
    inherit [_] iter_tavalue as super
    method! visit_aproj () p =
      (match p with
      | AProjLoans p -> if p.consumed <> [] || p.borrows <> [] then needed := true
      | AProjBorrows p -> if p.loans <> [] then needed := true
      | AEndedProjLoans p -> if p.consumed <> [] || p.borrows <> [] then needed := true
      | AEndedProjBorrows p -> if p.loans <> [] then needed := true
      | AEmpty -> needed := true);
      super#visit_aproj () p
    method! visit_AProjSharedBorrow () borrows =
      if borrows <> [] then needed := true;
      super#visit_AProjSharedBorrow () borrows
  end in
  List.iter (visitor#visit_tavalue ()) owner.avalues;
  !needed

(** The native declaration/type-analysis universe is the immutable universe of
    the executing compiler. This is the existing native/opaque-library trust
    boundary, not a new model or a proof of arbitrary Rust declarations.
    In particular this is NOT InterpExternalPermissions.projection_shape: tuple
    and declaration-backed closure types are legitimate native types here. *)
let check_type span (ctx : eval_ctx) (owner : abs) ty =
  let infos = ctx.type_ctx.type_infos in
  let check_decl (tref : type_decl_ref) =
    let decl = match TypeDeclId.Map.find_opt tref.id ctx.type_ctx.type_decls with
      | Some d -> d | None -> reject span "missing native type declaration" in
    require span (not decl.item_meta.has_errors) "erroneous native declaration";
    (match decl.kind with
    | Struct _ | Enum _ | Opaque -> ()
    | Union _ | Alias _ | TDeclError _ -> reject span "unsupported native declaration kind");
    (match decl.src with
    | NormalType | ClosureType _ -> ()
    | _ -> reject span "unsupported native declaration source");
    let args = tref.generics and params = decl.generics in
    require span
      (List.length args.regions = List.length params.regions
       && List.length args.types = List.length params.types
       && List.length args.const_generics = List.length params.const_generics
       && List.length args.trait_refs = List.length params.trait_clauses)
      "native generic arity mismatch";
    List.iter2 (fun (arg : constant_expr) (param : const_generic_param) ->
      require span (equal_ty arg.ty param.ty) "native const parameter type mismatch")
      args.const_generics params.const_generics;
    let info = match TypeDeclId.Map.find_opt tref.id infos with
      | Some i -> i | None -> reject span "missing native type analysis" in
    require span (List.length info.param_infos = List.length params.types)
      "native type-analysis parameter mismatch";
    let declared = RegionId.Set.of_list
      (List.map (fun (r : region_param) -> r.index) params.regions) in
    require span (RegionId.Set.subset info.mut_regions declared)
      "native type-analysis region mismatch"
  in
  let visitor = object
    inherit [_] iter_ty as super
    method! visit_region () = function
      | RVar (Free _) -> ()
      | _ -> reject span "non-free native region is unsupported"
    method! visit_constant_expr () c =
      (match c.kind, c.ty with
      | (CInteger _ | CBool _ | CChar _), TScalar scalar ->
          Invariants.check_literal_type span (TypesUtils.constant_expr_as_literal c) scalar
      | _ -> reject span "nonliteral native const argument is unsupported");
      super#visit_constant_expr () c
    method! visit_ty () t =
      (match t with
      | TScalar _ | TNever | TRef _ -> ()
      | TSlice (_, None) -> ()
      | TArray (_, length, None) ->
          require span (equal_ty length.ty TypesUtils.mk_usize_ty)
            "native array length is not usize"
      | TSlice (_, Some _) | TArray (_, _, Some _) ->
          reject span "native Sized witness needs separate validation"
      | TAdt tref ->
          let g = tref.generics in
          require span (g.trait_refs = []) "native trait witness needs separate validation";
          (match tref.builtin with
          | Some TTuple ->
              require span (tref.id = TypesUtils.unit_type_decl_id
                && g.regions = [] && g.const_generics = [])
                "malformed native tuple"
          | Some TBox ->
              require span (g.regions = [] && g.const_generics = []
                && List.length g.types = 1) "malformed native Box"
          | Some TStr ->
              require span (g.regions = [] && g.const_generics = [] && g.types = [])
                "malformed native str"
          | None -> check_decl tref)
      | TRawPtr _ | TFnDef _ | TFnPtr _ | TDynTrait _ | TPattern _
      | TVar _ | TTraitType _ | TPtrMetadata _ | TError _ ->
          reject span "unresolved or unsupported native type constructor");
      super#visit_ty () t
  end in
  visitor#visit_ty () ty;
  let info = TypesAnalysis.analyze_ty (Some span) infos ty in
  require span (not info.contains_static) "native type contains a static region";
  require span
    (not (TypesUtils.ty_has_mut_borrow_for_region_in_set infos owner.regions.owned ty))
    "native type has an owned mutable projection"

(** A symbolic shared reborrow remains a separate permission. This check
    admits its own native type; it does not turn it into a normal borrow
    projector, select it for cancellation, or alter its source value. *)
let check_shared_reborrow span (ctx : eval_ctx) (owner : abs) level
    (proj : symbolic_proj) =
  check_type span ctx owner proj.proj_ty;
  require span (not (AbsLevelSet.mem level owner.ended_subabs))
    "shared reborrow occurs at an ended level";
  require span
    (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
    "shared reborrow has an ended owned region";
  require span (TypesUtils.ty_has_regions_in_set owner.regions.owned proj.proj_ty)
    "shared reborrow type contains no owned region";
  let info = TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos proj.proj_ty in
  require span (not info.contains_nested_mut)
    "nested mutable shared reborrow is unsupported"

(** Retain an ordinary shared borrow independently of symbolic packet roots.
    The initial supported case has no borrowed data inside its referent; the
    native loan lookup and the original shared-borrow ID remain authoritative. *)
let check_retained_shared_borrow span (ctx : eval_ctx) (owner : abs) level
    (value : tavalue) =
  require span (level = 0 && not (AbsLevelSet.mem level owner.ended_subabs))
    "retained concrete shared borrow is not at a live root level";
  require span
    (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
    "retained concrete shared borrow has an ended owned region";
  match value.value, value.ty with
  | ABorrow (ASharedBorrow (PNone, bid, _)),
    TRef (RVar (Free region), referent, RShared) ->
      require span (RegionId.Set.mem region owner.regions.owned)
        "retained shared borrow does not own its reference region";
      check_type span ctx owner value.ty;
      require span
        (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent))
        "retained shared borrow has borrowed data in its referent";
      let shared = InterpBorrowsCore.lookup_shared_value span ctx.env bid in
      require span (equal_ty shared.ty (Substitute.erase_regions referent))
        "retained shared borrow disagrees with its native loan type";
      require span (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
        "retained shared borrow referent has concrete permissions";
      (Invariants.check_typing_invariant_visitor span ctx true)#visit_abs None
        { owner with avalues = [value]; cont = None }
  | _ -> reject span "retained concrete borrow is not an unmarked shared reference"

(** Concrete shared loans in a packet owner remain ordinary native loans.
    Restrict the retained leaf to borrow-free data and an ignored child. *)
let check_retained_shared_loan span (ctx : eval_ctx) (owner : abs) level
    (value : tavalue) =
  require span (level = 0 && not (AbsLevelSet.mem level owner.ended_subabs))
    "retained concrete shared loan is not at a live root level";
  require span
    (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
    "retained concrete shared loan has an ended owned region";
  match value.value, value.ty with
  | ALoan (ASharedLoan (PNone, _, shared, child)),
    TRef (RVar (Free region), referent, RShared) ->
      require span (RegionId.Set.mem region owner.regions.owned)
        "retained shared loan does not own its reference region";
      check_type span ctx owner value.ty;
      require span
        (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent))
        "retained shared loan has borrowed data in its referent";
      require span (equal_ty shared.ty (Substitute.erase_regions referent)
        && equal_ty child.ty referent)
        "retained shared loan payload type mismatch";
      require span (match child.value with AIgnored _ -> true | _ -> false)
        "retained concrete shared loan has a nonignored child";
      require span (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
        "retained shared loan referent has concrete permissions";
      (Invariants.check_typing_invariant_visitor span ctx true)#visit_abs None
        { owner with avalues = [value]; cont = None }
  | _ -> reject span "retained concrete loan is not an unmarked shared reference"

let check span (ctx : eval_ctx) (owner : abs) : certificate =
  let slots = ref [] in
  (* Preserve the native classifier's per-top-root, per-level mixed-polarity
     rejection without calling a Pure module from the interpreter. *)
  let polarities = ref [] in
  let polarity level borrow =
    let previous = List.assoc_opt level !polarities in
    (match previous with
    | None -> polarities := (level, borrow) :: !polarities
    | Some old -> require span (old = borrow)
        "mixed borrow and loan projections in one typed root level")
  in
  let typed path level role ty =
    check_type span ctx owner ty;
    slots := {path; level; role; ty} :: !slots
  in
  (* Extend the native typed-root SID/erased-type invariant to the history
     nodes admitted here. These are checks only, never runtime bindings or
     substitutions; edge metadata and child IDs remain independent. *)
  let sid_types = ref SymbolicValueId.Map.empty in
  let symbolic path level role sid ty =
    typed path level role ty;
    let erased = Substitute.erase_regions ty in
    (match SymbolicValueId.Map.find_opt sid !sid_types with
    | None -> sid_types := SymbolicValueId.Map.add sid erased !sid_types
    | Some previous -> require span (equal_ty previous erased)
        "one symbolic ID has inconsistent erased native types")
  in
  let no_nested_mut ty =
    let i = TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos ty in
    require span (not i.contains_nested_mut) "nested mutable symbolic projection is unsupported"
  in
  let live level =
    require span (not (AbsLevelSet.mem level owner.ended_subabs))
      "active projector occurs at an ended level";
    require span
      (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
      "active projector has an ended owned region"
  in
  let rec history path level entries =
    List.iteri (fun i ((m : mconsumed_symb), child) ->
      let path = path @ [string_of_int i] in
      symbolic (path @ ["metadata"]) level "history-metadata" m.sv_id m.proj_ty;
      (* An edge's metadata is not the child's type or a runtime binder. *)
      projector (path @ ["child"]) (level + 1) None child) entries
  and projector path level root_ty p =
    let own role sid ty =
      symbolic path level role sid ty;
      no_nested_mut ty;
      Option.iter (fun root ->
        require span (equal_ty (Substitute.erase_regions root) (Substitute.erase_regions ty))
          "typed projector wrapper disagrees with its own erased type") root_ty
    in
    match p with
    | AProjLoans p ->
        polarity level false;
        own "live-loan-own-type" p.proj.sv_id p.proj.proj_ty; live level;
        require span (TypesUtils.ty_has_regions_in_set owner.regions.owned p.proj.proj_ty)
          "active loan projector type contains no owned region";
        history (path @ ["consumed"]) level p.consumed;
        history (path @ ["borrows"]) level p.borrows
    | AProjBorrows p ->
        polarity level true;
        own "live-borrow-own-type" p.proj.sv_id p.proj.proj_ty; live level;
        require span (TypesUtils.ty_has_free_regions p.proj.proj_ty)
          "active borrow projector type contains no free region";
        history (path @ ["loans"]) level p.loans
    | AEndedProjLoans p ->
        polarity level false;
        own "ended-loan-own-type" p.proj p.proj_ty;
        history (path @ ["consumed"]) level p.consumed;
        history (path @ ["borrows"]) level p.borrows
    | AEndedProjBorrows p ->
        polarity level true;
        own "ended-borrow-own-type" p.mvalues.consumed p.proj_ty;
        symbolic (path @ ["given_back_metadata"]) level "given-back-metadata"
          p.mvalues.given_back.sv_id p.mvalues.given_back.sv_ty;
        history (path @ ["loans"]) level p.loans
    | AEmpty -> ()
  and avalue path level (v : tavalue) =
    typed path level "typed-wrapper" v.ty;
    match v.value with
    | AAdt a ->
        (* The native checker below validates the real variant and full typed
           projected field representation, not a filtered Pure tuple. *)
        List.iteri (fun i f -> avalue (path @ ["field";string_of_int i]) level f) a.fields
    | AIgnored None -> ()
    | ASymbolic (pm,p) ->
        require span (pm = PNone) "marked A projector is unsupported";
        no_nested_mut v.ty;
        projector (path @ ["packet"]) level (Some v.ty) p
    | ALoan (ASharedLoan _) ->
        require span (match path with ["avalue"; _] -> true | _ -> false)
          "retained concrete shared loan must be a top-level root";
        check_retained_shared_loan span ctx owner level v
    | ABorrow (ASharedBorrow _) ->
        require span (match path with ["avalue"; _] -> true | _ -> false)
          "retained concrete shared borrow must be a top-level root";
        check_retained_shared_borrow span ctx owner level v
    | ABorrow (AProjSharedBorrow borrows) ->
        (match v.ty with
        | TRef (RVar (Free outer), _, RShared) ->
            require span (not (RegionId.Set.mem outer owner.regions.owned))
              "shared reborrow wrapper owns its outer region"
        | _ -> reject span "shared reborrow wrapper is not a shared reference");
        List.iteri (fun i -> function
          | AsbProjReborrows proj ->
              check_shared_reborrow span ctx owner level proj;
              symbolic (path @ ["shared_reborrow"; string_of_int i]) level
                "shared-reborrow-own-type" proj.sv_id proj.proj_ty
          | AsbBorrow _ ->
              reject span "concrete shared reborrow needs separate admission") borrows
    | ABorrow (AEndedIgnoredMutBorrow b) ->
        polarity level true;
        (match v.ty with
        | TRef (RVar (Free r), target, RMut) ->
            require span (not (RegionId.Set.mem r owner.regions.owned))
              "ended ignored mutable wrapper owns its outer region";
            require span (equal_ty b.child.ty target && equal_ty b.given_back.ty target)
              "ended ignored mutable wrapper child type mismatch"
        | _ -> reject span "ended ignored mutable wrapper requires a native mutable reference");
        symbolic (path @ ["given_back_metadata"]) level "given-back-metadata"
          b.given_back_meta.sv_id b.given_back_meta.sv_ty;
        avalue (path @ ["child"]) level b.child;
        avalue (path @ ["given_back"]) (level + 1) b.given_back
    | ABorrow (AIgnoredMutBorrow (None,child)) ->
        polarity level true;
        avalue (path @ ["child"]) level child
    | ALoan (AIgnoredSharedLoan child) ->
        polarity level false;
        (match v.ty with
        | TRef (RVar (Free outer), target, RShared) ->
            require span (not (RegionId.Set.mem outer owner.regions.owned))
              "ignored shared-loan wrapper owns its outer region";
            require span (equal_ty target child.ty)
              "ignored shared-loan wrapper child type mismatch"
        | _ -> reject span "ignored shared-loan wrapper is not a shared reference");
        avalue (path @ ["child"]) level child
    | ALoan (AIgnoredMutLoan (None,child)) ->
        polarity level false;
        avalue (path @ ["child"]) level child
    | AIgnored (Some _) | ABorrow _ | ALoan _ ->
        reject span "concrete, tracked, or unsupported A wrapper needs separate admission"
  in
  List.iteri (fun i v ->
    polarities := [];
    avalue ["avalue";string_of_int i] 0 v) owner.avalues;
  (* Call the visitor directly: opt_type_check_abs and the Config.sanity_checks
     switch are deliberately NOT used. This supplements, not replaces, the
     explicit own-history-type and metadata checks above. *)
  (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None owner;
  {owner; slots=List.rev !slots}
