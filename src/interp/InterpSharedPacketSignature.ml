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
    method! visit_AIgnoredMutBorrow () bid child =
      if Option.is_some bid then needed := true;
      super#visit_AIgnoredMutBorrow () bid child
    method! visit_aloan_content () loan =
      (match loan with AEndedIgnoredMutLoan _ | AIgnoredMutLoan (Some _,_) -> needed := true | _ -> ());
      super#visit_aloan_content () loan
  end in
  List.iter (visitor#visit_tavalue ()) owner.avalues;
  !needed

(** Ended ignored mutable loans retain two distinct sub-abstraction levels.
    This traversal locates only concrete leaves under their original ADT fields;
    it never visits synthesis metadata or turns the two levels into one edge. *)
let retained_ended_shared_leaf_location (owner : abs) path level (value : tavalue) =
  let rec visit current current_level origin (v : tavalue) =
    if current = path && current_level = level && v = value then
      match v.value with
      | ALoan (ASharedLoan _ | AEndedSharedLoan _)
      | ABorrow (ASharedBorrow _ | AEndedSharedBorrow) -> origin
      | _ -> None
    else
      match v.value with
      | AAdt a ->
          List.find_map (fun (i, field) ->
            visit (current @ ["field"; string_of_int i]) current_level origin field)
            (List.mapi (fun i field -> (i, field)) a.fields)
      | ALoan (AEndedIgnoredMutLoan ended) ->
          (match visit (current @ ["child"]) current_level
                   (Some (current, current_level, false)) ended.child with
          | Some _ as found -> found
          | None -> visit (current @ ["given_back"]) (current_level + 1)
              (Some (current, current_level, true)) ended.given_back)
      | _ -> None
  in
  List.find_map (fun (i, root) -> visit ["avalue"; string_of_int i] 0 None root)
    (List.mapi (fun i root -> (i, root)) owner.avalues)

let has_retained_ended_mut_loan (owner : abs) =
  let found = ref false in
  let visitor = object
    inherit [_] iter_tavalue as super
    method! visit_aloan_content () loan =
      (match loan with AEndedIgnoredMutLoan _ -> found := true | _ -> ());
      super#visit_aloan_content () loan
  end in
  List.iter (visitor#visit_tavalue ()) owner.avalues;
  !found

(** Keep a tracked parent-return subscription even after its child becomes
    empty. It is not itself a cancellable borrow permission. *)
let has_retained_ignored_mut_wrapper (owner : abs) =
  let found = ref false in
  let visitor = object
    inherit [_] iter_tavalue as super
    method! visit_AIgnoredMutBorrow () bid child =
      if Option.is_some bid then found := true;
      super#visit_AIgnoredMutBorrow () bid child
    method! visit_AIgnoredMutLoan () bid child =
      if Option.is_some bid then found := true;
      super#visit_AIgnoredMutLoan () bid child
  end in
  List.iter (visitor#visit_tavalue ()) owner.avalues;
  !found

(** Locate an intact native shared-loan leaf through native ADT fields and
    at most one ignored shared-loan wrapper. Both preserve the native level;
    the ignored outer reference carries no concrete permission of its own.
    Never traverse another loan/borrow wrapper or synthesis metadata. *)
let retained_adt_shared_loan_root (owner : abs) path level (value : tavalue) =
  let rec contains current ignored_wrapper (v : tavalue) =
    if current = path && v == value then
      (match v.value with ALoan (ASharedLoan _ | AEndedSharedLoan _) -> true | _ -> false)
    else match v.value with
      | AAdt adt -> List.exists (fun (i, field) ->
          contains (current @ ["field"; string_of_int i]) ignored_wrapper field)
          (List.mapi (fun i field -> i,field) adt.fields)
      | ALoan (AIgnoredSharedLoan child) when not ignored_wrapper ->
          contains (current @ ["child"]) true child
      | _ -> false
  in
  if level <> 0 then None
  else List.find_map (fun (i, (root : tavalue)) -> match root.value with
    | AAdt _ | ALoan (AIgnoredSharedLoan _) ->
        if contains ["avalue"; string_of_int i] false root then Some root else None
    | _ -> None) (List.mapi (fun i root -> i,root) owner.avalues)

let retained_shared_leaf_path span ctx (owner : abs) path level value =
  match path with
  | ["avalue"; _] -> level = 0
  | _ ->
      if Option.is_some (retained_ended_shared_leaf_location owner path level value) then true
      else match retained_adt_shared_loan_root owner path level value with
        | None -> false
        | Some root ->
            (* Check the complete original wrapper tree, including its native
               variant, ignored reference and every field. The leaf's permission and
               referent checks still run in the caller; no node is rewritten. *)
            (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None
              {owner with avalues=[root];cont=None};
            true

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

(** Inspection-only loan lookup in a join context. Native operational lookup
    rejects every marked loan it traverses, even an unrelated one. Inventory
    current A/concrete loans with their own marker and native sublevel instead;
    metadata and E continuations are deliberately not current loan sources. *)
let collect_retained_shared_values ?(include_both_markers=false) span ~type_infos ~ended_regions env marker bid =
  let candidates = ref [] in
  let remember (owner,level,_) loan_marker lid (shared : tvalue option) =
    if lid=bid && (loan_marker=marker || loan_marker=PNone
      || (include_both_markers && marker=PNone)) then begin
      Option.iter (fun (owner:abs) ->
        require span (not (AbsLevelSet.mem level owner.ended_subabs))
          "retained shared borrow resolves to a loan at an ended level";
        (* Native concrete shared permission is represented by its loan ID.
           A branch union can mark the ghost outer region ended on the other
           side. Borrow-free payloads contain no symbolic region permission;
           borrowed referents retain the stricter existing lifetime boundary. *)
        let borrow_free=match shared with
          | Some value -> not (TypesUtils.ty_has_borrows (Some span) type_infos value.ty)
          | None -> false in
        require span (borrow_free || RegionId.Set.is_empty
          (RegionId.Set.inter owner.regions.owned ended_regions))
          "retained borrowed shared value resolves to ended owned regions") owner;
      candidates := (loan_marker,shared) :: !candidates
    end
  in
  let visitor = object (self)
    inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
    method incr_level (owner,level,marker) = owner,level+1,marker
    method! visit_AMutLoan state loan_marker lid child =
      remember state loan_marker lid None;
      self#visit_tavalue state child
    method! visit_ASharedLoan ((owner,level,_) as state) loan_marker lid shared child =
      remember state loan_marker lid (Some shared);
      self#visit_tvalue (owner,level,loan_marker) shared;
      self#visit_tavalue state child
    method! visit_VMutLoan ((_,_,loan_marker) as state) lid =
      remember state loan_marker lid None
    method! visit_VSharedLoan ((_,_,loan_marker) as state) lid shared =
      remember state loan_marker lid (Some shared);
      super#visit_VSharedLoan state lid shared
  end in
  List.iter (function
    | EAbs owner ->
        List.iter (visitor#visit_tavalue (Some owner,0,PNone)) owner.avalues
    | EBinding (_,value) -> visitor#visit_tvalue (None,0,PNone) value
    | EFrame -> ()) env;
  !candidates

let lookup_retained_shared_value_in_env ?(allow_joined_typing=false) span
    ~type_infos ~ended_regions env marker bid =
  let candidates=collect_retained_shared_values ~include_both_markers:allow_joined_typing
    span ~type_infos ~ended_regions env marker bid in
  match candidates with
  | [loan_marker,Some shared] when loan_marker=marker || loan_marker=PNone -> shared
  | [(PLeft,Some left);(PRight,Some right)]
  | [(PRight,Some right);(PLeft,Some left)]
    when allow_joined_typing && marker=PNone && equal_tvalue left right -> left
  | _ ->
      let all=collect_retained_shared_values ~include_both_markers:true
        span ~type_infos ~ended_regions env PNone bid in
      let describe (marker,payload)=show_proj_marker marker ^ ": "
        ^ (match payload with None -> "mutable loan" | Some value -> show_tvalue value) in
      reject span ("retained shared borrow needs one compatible current shared loan: marker="
        ^ show_proj_marker marker ^ " loan=" ^ BorrowId.to_string bid
        ^ " candidates=" ^ string_of_int (List.length candidates)
        ^ "\nall original current loan candidates:\n" ^ String.concat "\n" (List.map describe all))

(** Complete read-only dependency inventory during a native join. An
    unmarked concrete borrow can refer to the original shared value on each
    branch. Return both original values with their branch identity; unlike a
    typing reader, this API must not select a representative and hide the
    other branch's runtime dependencies. Every candidate retains the same
    native owner/sublevel checks as the strict single-value lookup. *)
let lookup_retained_shared_values_for_inventory_in_env span
    ~type_infos ~ended_regions env marker bid =
  let candidates=collect_retained_shared_values ~include_both_markers:true
    span ~type_infos ~ended_regions env marker bid in
  match candidates with
  | [loan_marker,Some shared] when loan_marker=marker || loan_marker=PNone ->
      [marker,shared]
  | [(PLeft,Some left);(PRight,Some right)]
  | [(PRight,Some right);(PLeft,Some left)]
    when marker=PNone && equal_ty left.ty right.ty
      && not (TypesUtils.ty_has_borrows (Some span) type_infos left.ty) ->
      [PLeft,left;PRight,right]
  | _ ->
      (* Preserve the strict reader's exact failure for every other shape. *)
      [marker,lookup_retained_shared_value_in_env span
        ~type_infos ~ended_regions env marker bid]

let lookup_retained_shared_value span (ctx : eval_ctx) marker bid =
  lookup_retained_shared_value_in_env span ~type_infos:ctx.type_ctx.type_infos
    ~ended_regions:ctx.ended_regions ctx.env marker bid

(** A borrowed shared referent can stay symbolic when its live shared regions
    belong entirely outside this owner. Keep its original SID and full native
    type: runtime inventory still observes it, and union-mask checks see the
    same regions in the enclosing reference type. No hidden permission becomes
    an ordinary packet root or is silently expanded/copied here. *)
let check_retained_shared_referent ~marker span (ctx : eval_ctx) (owner : abs)
    referent (shared : tvalue) =
  if TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent then (
    let checked condition message =
      if not condition then reject span
        (message ^ "\nreferent: " ^ InterpUtils.ty_to_string ctx referent
         ^ "\nshared payload: " ^ InterpUtils.tvalue_to_string ctx shared
         ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner)
    in
    checked (equal_ty shared.ty (Substitute.erase_regions referent))
      "borrowed shared referent has a different erased type";
    check_type span ctx owner referent;
    let info = TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos referent in
    checked (not (info.contains_mut_borrow || info.contains_static))
      "borrowed shared referent is not entirely shared and nonstatic";
    let regions = TypesUtils.ty_regions referent in
    checked (RegionId.Set.is_empty (RegionId.Set.inter regions ctx.ended_regions))
      "borrowed shared referent contains an ended region";
    checked (RegionId.Set.is_empty (RegionId.Set.inter regions owner.regions.owned))
      "borrowed shared referent contains an owner region";
    match shared.value,referent with
    | VSymbolic symbolic,_ ->
        checked (equal_ty symbolic.sv_ty referent)
          "borrowed shared symbolic referent has a different full native type"
    | VBorrow(VSharedBorrow(bid,_)),TRef(RVar(Free _),target,RShared) ->
        (* This is a real current permission, not ignored metadata. Its
           original ID is indexed under the enclosing loan's marker; runtime
           closure follows this very borrow to its original current payload. *)
        checked (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos target))
          "retained shared-reference payload has a nested target";
        let borrowed=lookup_retained_shared_values_for_inventory_in_env span
          ~type_infos:ctx.type_ctx.type_infos ~ended_regions:ctx.ended_regions
          ctx.env marker bid in
        (* After joining the outer loan, its unmarked payload can still have
           both original inner loan branches. Inspect every original value;
           never choose a representative or weaken operational lookup. *)
        List.iter (fun (_,(borrowed:tvalue)) ->
          checked (equal_ty borrowed.ty (Substitute.erase_regions target))
            "retained shared-reference payload disagrees with its current loan";
          checked (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx borrowed))
            "retained shared-reference target contains concrete permissions") borrowed
    | _ -> checked false "borrowed shared referent is neither exact symbolic nor a direct shared reference")

let retained_shared_payload_has_only_checked_permission (shared:tvalue) =
  match shared.value with VBorrow(VSharedBorrow _) -> true | _ -> false

(** Read-only typing of a current concrete binding during a native join.
    An unmarked runtime borrow can have one original loan on each branch.
    Admit only the complete, unique Left/Right pair with exactly equal full
    payloads and types; the collector checks each original owner and level.
    No single marked loan, mutable loan, or additional occurrence is accepted.
    Operational/inventory callers retain the strict lookup above. *)
let lookup_retained_shared_value_for_typing span (ctx : eval_ctx) marker bid =
  lookup_retained_shared_value_in_env ~allow_joined_typing:true span
    ~type_infos:ctx.type_ctx.type_infos ~ended_regions:ctx.ended_regions
    ctx.env marker bid

(** Type-only inspection of the complete native join relation. A current
    unmarked borrow may refer to different branch values (for example Nil and
    Cons). For a unique Left/Right pair, only their common borrow-free type is
    returned. No payload is selected, joined, or made available to the caller;
    ordinary permission lookup and native value joining remain unchanged. *)
let lookup_retained_shared_type_for_typing span (ctx : eval_ctx) marker bid : ty =
  let candidates=collect_retained_shared_values ~include_both_markers:true span
    ~type_infos:ctx.type_ctx.type_infos ~ended_regions:ctx.ended_regions
    ctx.env marker bid in
  match candidates with
  | [loan_marker,Some shared] when loan_marker=marker || loan_marker=PNone -> shared.ty
  | [(PLeft,Some left);(PRight,Some right)]
  | [(PRight,Some right);(PLeft,Some left)]
    when marker=PNone && equal_ty left.ty right.ty
      && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos left.ty) -> left.ty
  | _ ->
      reject span ("typing needs one compatible shared loan or a complete borrow-free branch pair: marker="
        ^ show_proj_marker marker ^ " loan=" ^ BorrowId.to_string bid
        ^ " candidates=" ^ string_of_int (List.length candidates))

(** Exact UMut lookup for transient invariant checking. Unrelated marked
    shared borrows are traversed as ordinary current nodes, never mistaken for
    the requested mutable permission. The returned type is taken from its
    original payload; metadata/captured environments are not candidate sources. *)
let lookup_retained_mut_borrow_type span (ctx : eval_ctx) marker bid =
  let candidates = ref [] in
  let remember (owner,level,_) borrow_marker id ty =
    if id=bid && (borrow_marker=marker || borrow_marker=PNone) then begin
      Option.iter (fun (owner:abs) ->
        require span (not (AbsLevelSet.mem level owner.ended_subabs))
          "mutable loan resolves to a borrow at an ended level";
        require span (RegionId.Set.is_empty
          (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
          "mutable loan resolves to a borrow with ended owned regions") owner;
      candidates := ty :: !candidates
    end in
  let visitor = object (self)
    inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
    method incr_level (owner,level,marker) = owner,level+1,marker
    method! visit_AMutBorrow state borrow_marker id (child : tavalue) =
      remember state borrow_marker id (Substitute.erase_regions child.ty);
      self#visit_tavalue state child
    method! visit_ASharedLoan ((owner,level,_) as state) loan_marker _ shared child =
      self#visit_tvalue (owner,level,loan_marker) shared;
      self#visit_tavalue state child
    method! visit_VMutBorrow ((_,_,borrow_marker) as state) id (child : tvalue) =
      remember state borrow_marker id child.ty;
      super#visit_VMutBorrow state id child
  end in
  List.iter (function
    | EAbs owner -> List.iter (visitor#visit_tavalue (Some owner,0,PNone)) owner.avalues
    | EBinding (_,value) -> visitor#visit_tvalue (None,0,PNone) value
    | EFrame -> ()) ctx.env;
  match !candidates with
  | [ty] -> ty
  | _ -> reject span ("mutable loan needs one compatible current UMut borrow: marker="
      ^ show_proj_marker marker ^ " borrow=" ^ BorrowId.to_string bid
      ^ " candidates=" ^ string_of_int (List.length !candidates))

(** Retain an ordinary shared borrow independently of symbolic packet roots.
    Borrowed referents remain exact symbolic values over other live shared
    regions; native loan lookup and the shared-borrow ID stay authoritative. *)
let check_retained_shared_borrow ?(allow_marked=false) span (ctx : eval_ctx) (owner : abs) level
    (value : tavalue) =
  require span (not (AbsLevelSet.mem level owner.ended_subabs))
    "retained concrete shared borrow is not at a live sub-abstraction level";
  match value.value, value.ty with
  | ABorrow (ASharedBorrow (marker, bid, _)),
    TRef (RVar (Free region), referent, RShared) when allow_marked || marker=PNone ->
      require span (RegionId.Set.mem region owner.regions.owned)
        "retained shared borrow does not own its reference region";
      (* For a borrow-free referent, native current concrete IDs and the
         unended sublevel determine the permission. The outer region is ghost
         type evidence and can be ended in the other joined branch. *)
      require span (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
        || RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
        "retained borrowed shared referent has an ended owned region";
      check_type span ctx owner value.ty;
      let shared =
        if allow_marked then lookup_retained_shared_value span ctx marker bid
        else InterpBorrowsCore.lookup_shared_value span ctx.env bid in
      check_retained_shared_referent ~marker span ctx owner referent shared;
      require span (equal_ty shared.ty (Substitute.erase_regions referent))
        "retained shared borrow disagrees with its native loan type";
      require span (retained_shared_payload_has_only_checked_permission shared
        || not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
        "retained shared borrow referent has concrete permissions";
      (* The only optional native lookup on this leaf is the same erased-type
         check above. Avoid repeating its marker-blind lookup during inspection;
         all native local typing/ownership checks still run on the original leaf. *)
      (Invariants.check_typing_invariant_visitor span ctx (not allow_marked))#visit_abs None
        { owner with avalues = [value]; cont = None }
  | _ -> reject span "retained concrete borrow is not an unmarked shared reference"

(** Concrete shared loans in a packet owner remain ordinary native loans.
    Retain an ignored child and either borrow-free data or the exact external
    symbolic shared referent admitted above. *)
let check_retained_shared_loan ?(allow_marked=false) span (ctx : eval_ctx) (owner : abs) level
    (value : tavalue) =
  require span (not (AbsLevelSet.mem level owner.ended_subabs))
    "retained concrete shared loan is not at a live sub-abstraction level";
  match value.value, value.ty with
  | ALoan (ASharedLoan (marker, _, shared, child)),
    TRef (RVar (Free region), referent, RShared) when allow_marked || marker=PNone ->
      require span (RegionId.Set.mem region owner.regions.owned)
        "retained shared loan does not own its reference region";
      (* For a borrow-free referent, native current concrete IDs and the
         unended sublevel determine the permission. The outer region is ghost
         type evidence and can be ended in the other joined branch. *)
      require span (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
        || RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
        "retained borrowed shared referent has an ended owned region";
      check_type span ctx owner value.ty;
      check_retained_shared_referent ~marker span ctx owner referent shared;
      require span (equal_ty shared.ty (Substitute.erase_regions referent)
        && equal_ty child.ty referent)
        "retained shared loan payload type mismatch";
      require span (match child.value with AIgnored _ -> true | _ -> false)
        "retained concrete shared loan has a nonignored child";
      require span (retained_shared_payload_has_only_checked_permission shared
        || not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
        "retained shared loan referent has concrete permissions";
      (* The strict read-only lookup above checks the inner permission in
         marked contexts; repeat all native local type checks on the real tree. *)
      (Invariants.check_typing_invariant_visitor span ctx (not allow_marked))#visit_abs None
        { owner with avalues = [value]; cont = None }
  | _ -> reject span "retained concrete loan is not an unmarked shared reference"

(** Some bid is the native parent-return notification from apply_proj_borrows,
    not another UMut borrow. Validate the original parent permission and loan;
    retain the ID, wrapper and parent edges for give_back_value's A/E transition. *)
let check_tracked_ignored_mut ?(allow_marked=false) ~historical_shared ~is_borrow span (ctx : eval_ctx)
    (owner : abs) level bid ty child_ty =
  let checked condition message = require span condition
      (message ^ " (tracked reference=" ^ BorrowId.to_string bid
       ^ ", owner=" ^ AbsId.to_string owner.abs_id ^ ")") in
  let outer, target = match ty with
    | TRef (RVar (Free outer), target, RMut) -> outer,target
    | _ -> reject span "tracked ignored reference needs its native mutable-reference type" in
  (* A retained child of an ended ignored-borrow wrapper describes the earlier
     projection, not the parent's new shared projection scope after a join.
     Keep both complete types and all subscription IDs. Only the mutable outer
     permission must coincide; any mutable referent or different carrier is
     rejected. This is observation of historical metadata, not region unification. *)
  let parent_type_matches actual =
    equal_ty actual ty ||
    (historical_shared
     && Sys.getenv_opt "AENEAS_EXPERIMENTAL_HISTORICAL_SHARED_SUBSCRIPTION" = Some "1"
     && match actual with
        | TRef (RVar (Free actual_outer),actual_target,RMut) ->
            if actual_outer=outer
               && not (TypesUtils.ty_has_mut_borrows ctx.type_ctx.type_infos target)
               && not (TypesUtils.ty_has_mut_borrows ctx.type_ctx.type_infos actual_target)
               && equal_ty (Substitute.erase_regions target) (Substitute.erase_regions actual_target)
            then (
              check_type span ctx owner actual;
              RegionId.Set.is_empty (RegionId.Set.inter (TypesUtils.ty_regions actual) ctx.ended_regions))
            else false
        | _ -> false)
  in
  check_type span ctx owner ty;
  checked (equal_ty target child_ty) "tracked ignored reference child type changed";
  checked (not (RegionId.Set.mem outer owner.regions.owned))
    "tracked ignored reference owns its outer region";
  checked (TypesUtils.ty_has_regions_in_set owner.regions.owned target)
    "tracked ignored reference referent has no owned projection";
  checked (not (AbsLevelSet.mem level owner.ended_subabs)
    && RegionId.Set.is_empty (RegionId.Set.inter (TypesUtils.ty_regions ty) ctx.ended_regions))
    "tracked ignored reference contains an ended level or region";
  let rec ancestors seen pending = match pending with
    | [] -> seen
    | id::rest when AbsId.Set.mem id seen -> ancestors seen rest
    | id::rest ->
        let parent = match ctx_lookup_abs_opt ctx id with
          | Some parent -> parent | None -> reject span "tracked ignored reference parent is absent" in
        ancestors (AbsId.Set.add id seen) (AbsId.Set.elements parent.parents @ rest) in
  let ancestors = ancestors AbsId.Set.empty (AbsId.Set.elements owner.parents) in
  let parents = ref [] in
  AbsId.Set.iter (fun id ->
    let parent=ctx_lookup_abs ctx id in
    let visitor=object
      inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
      method incr_level level = level+1
      method! visit_tavalue level (value : tavalue) =
        (match value.value with
        | ABorrow (AMutBorrow (marker,id,_)) when is_borrow && id=bid ->
            checked (allow_marked || marker=PNone) "marked parent borrow is unsupported";
            checked (parent_type_matches value.ty && RegionId.Set.mem outer parent.regions.owned
              && not (AbsLevelSet.mem level parent.ended_subabs))
              "tracked ignored reference disagrees with its live parent permission";
            parents := marker :: !parents
        | ALoan (AMutLoan (marker,id,_)) when not is_borrow && id=bid ->
            checked (allow_marked || marker=PNone) "marked parent loan is unsupported";
            checked (equal_ty value.ty ty && RegionId.Set.mem outer parent.regions.owned
              && not (AbsLevelSet.mem level parent.ended_subabs))
              "tracked ignored loan disagrees with its live parent permission";
            parents := marker :: !parents
        | _ -> ());
        super#visit_tavalue level value
    end in List.iter (visitor#visit_tavalue 0) parent.avalues) ancestors;
  let marker=match !parents with
    | [marker] -> marker
    | _ -> reject span ("tracked ignored reference needs one original parent mutable permission: "
        ^ BorrowId.to_string bid ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner) in
  let loans=ref 0 in
  let remember (loan_owner,level) loan_marker id loan_ty =
    if id=bid && (loan_marker=marker || loan_marker=PNone) then begin
      checked (equal_ty loan_ty (Substitute.erase_regions target))
        "tracked ignored reference disagrees with its mutable counterpart type";
      Option.iter (fun (loan_owner:abs) ->
        checked (not (AbsLevelSet.mem level loan_owner.ended_subabs)
          && RegionId.Set.is_empty (RegionId.Set.inter loan_owner.regions.owned ctx.ended_regions))
          "tracked ignored reference resolves to an ended mutable counterpart") loan_owner;
      incr loans
    end in
  let visitor=object
    inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
    method incr_level (owner,level) = owner,level+1
    method! visit_AMutLoan state marker id (child:tavalue) =
      if is_borrow then remember state marker id (Substitute.erase_regions child.ty);
      super#visit_AMutLoan state marker id child
    method! visit_AMutBorrow state marker id (child:tavalue) =
      if not is_borrow then remember state marker id (Substitute.erase_regions child.ty);
      super#visit_AMutBorrow state marker id child
    method! visit_tvalue state (value:tvalue) =
      (match value.value with
      | VLoan (VMutLoan id) when is_borrow -> remember state PNone id value.ty
      | VBorrow (VMutBorrow (id,child)) when not is_borrow -> remember state PNone id child.ty
      | _ -> ());
      super#visit_tvalue state value
  end in
  List.iter (function
    | EAbs abs -> List.iter (visitor#visit_tavalue (Some abs,0)) abs.avalues
    | EBinding (_,value) -> visitor#visit_tvalue (None,0) value
    | EFrame -> ()) ctx.env;
  checked (!loans=1) "tracked ignored reference needs one current mutable counterpart"

let check_tracked_ignored_mut_borrow ?allow_marked =
  check_tracked_ignored_mut ?allow_marked ~historical_shared:false ~is_borrow:true

let check_tracked_ignored_mut_loan ?allow_marked =
  check_tracked_ignored_mut ?allow_marked ~historical_shared:false ~is_borrow:false

let check ?(allow_marked=false) span (ctx : eval_ctx) (owner : abs) : certificate =
  let slots = ref [] in
  let current_value = ref None in
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
  let live level ty =
    require span (not (AbsLevelSet.mem level owner.ended_subabs))
      "active projector occurs at an ended level";
    require span
      (RegionId.Set.is_empty (RegionId.Set.inter
        (RegionId.Set.inter owner.regions.owned (TypesUtils.ty_regions ty)) ctx.ended_regions))
      "active projector type has an ended owned region"
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
        own "live-loan-own-type" p.proj.sv_id p.proj.proj_ty; live level p.proj.proj_ty;
        require span (TypesUtils.ty_has_regions_in_set owner.regions.owned p.proj.proj_ty)
          "active loan projector type contains no owned region";
        history (path @ ["consumed"]) level p.consumed;
        history (path @ ["borrows"]) level p.borrows
    | AProjBorrows p ->
        polarity level true;
        own "live-borrow-own-type" p.proj.sv_id p.proj.proj_ty; live level p.proj.proj_ty;
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
  and avalue ?(historical_shared=false) path level (v : tavalue) =
    current_value := Some (path,level,v);
    typed path level "typed-wrapper" v.ty;
    match v.value with
    | AAdt a ->
        (* The native checker below validates the real variant and full typed
           projected field representation, not a filtered Pure tuple. *)
        List.iteri (fun i f -> avalue ~historical_shared (path @ ["field";string_of_int i]) level f) a.fields
    | AIgnored None -> ()
    | AIgnored (Some ({value=VBorrow(VSharedBorrow _);_} as metadata))
      when level=0 && (match path with ["avalue";_]->true|_->false) ->
        (match v.ty with
        | TRef (RVar(Free outer),referent,RShared) ->
            require span (not (RegionId.Set.mem outer owner.regions.owned)
              && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent))
              "ignored root shared metadata contains an owned or nested reference"
        | _ -> reject span "ignored shared metadata lost its full shared reference type");
        require span (equal_ty metadata.ty (Substitute.erase_regions v.ty))
          "ignored shared metadata disagrees with its native erased type";
        (Invariants.check_typing_invariant_visitor span ctx false)#visit_tvalue None metadata;
        (* Native top-root consumption uses filter=true, so AIgnored does not
           read this historical borrow. Keep the original typed metadata; do
           not perform a current-loan lookup or register it as a permission.
           This rule deliberately excludes nested ADT fields, whose metadata
           can be consumed with filter=false. *)
        slots := {path=path@["ignored_metadata"];level;
          role="ignored-root-shared-metadata";ty=metadata.ty} :: !slots
    | AIgnored (Some metadata)
      when not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos v.ty) ->
        require span (equal_ty metadata.ty (Substitute.erase_regions v.ty))
          "ignored metadata disagrees with its native erased type";
        (match metadata.value with
        | VSymbolic symbolic ->
            require span (equal_ty symbolic.sv_ty v.ty)
              "ignored symbolic metadata disagrees with its full native type"
        | _ -> ());
        require span (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx metadata))
          "ignored metadata contains current borrow/loan permissions";
        (Invariants.check_typing_invariant_visitor span ctx false)#visit_tvalue None metadata;
        (* Retain the original metadata as synthesis data, never a new current
           permission or symbolic binding. The enclosing typed tree is unchanged. *)
        slots := { path = path @ ["ignored_metadata"]; level;
                   role = "ignored-concrete-metadata"; ty = metadata.ty } :: !slots
    | ASymbolic (pm,p) ->
        require span (allow_marked || pm = PNone) "marked A projector is unsupported";
        no_nested_mut v.ty;
        projector (path @ ["packet"]) level (Some v.ty) p
    | ALoan (ASharedLoan _) ->
        require span (retained_shared_leaf_path span ctx owner path level v)
          "retained concrete shared loan is outside a supported typed root";
        check_retained_shared_loan ~allow_marked span ctx owner level v
    | ABorrow (ASharedBorrow _) ->
        require span (retained_shared_leaf_path span ctx owner path level v)
          "retained concrete shared borrow is outside a supported typed root";
        check_retained_shared_borrow ~allow_marked span ctx owner level v
    | ABorrow AEndedSharedBorrow ->
        require span (retained_shared_leaf_path span ctx owner path level v)
          "ended shared borrow is outside a supported typed root";
        (match v.ty with
        | TRef (RVar (Free region), _, RShared) ->
            require span (RegionId.Set.mem region owner.regions.owned)
              "ended shared borrow does not own its original reference region"
        | _ -> reject span "ended shared borrow lost its native reference type")
    | ALoan (AEndedSharedLoan (shared,child)) ->
        require span (retained_shared_leaf_path span ctx owner path level v)
          "ended shared loan is outside a supported typed root";
        (match v.ty with
        | TRef (RVar (Free region), referent, RShared) ->
            require span (RegionId.Set.mem region owner.regions.owned)
              "ended shared loan does not own its original reference region";
            require span (equal_ty shared.ty (Substitute.erase_regions referent)
              && equal_ty child.ty referent
              && (match child.value with AIgnored _ -> true | _ -> false))
              "ended shared loan changed its original payload or child type";
            require span (not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
              && not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
              "ended retained shared loan has a borrowed referent"
        | _ -> reject span "ended shared loan lost its native reference type")
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
        avalue ~historical_shared:true (path @ ["child"]) level b.child;
        avalue (path @ ["given_back"]) (level + 1) b.given_back
    | ABorrow (AIgnoredMutBorrow (Some bid,child)) ->
        check_tracked_ignored_mut ~allow_marked ~historical_shared ~is_borrow:true
          span ctx owner level bid v.ty child.ty;
        polarity level true;
        avalue (path @ ["child"]) level child
    | ABorrow (AIgnoredMutBorrow (None,child)) ->
        polarity level true;
        avalue (path @ ["child"]) level child
    | ALoan (AEndedIgnoredMutLoan ended) ->
        polarity level false;
        (match v.ty with
        | TRef (RVar (Free outer), target, RMut) ->
            require span (not (RegionId.Set.mem outer owner.regions.owned))
              "ended ignored mutable loan owns its outer region";
            require span (equal_ty target ended.child.ty && equal_ty target ended.given_back.ty)
              "ended ignored mutable loan child type mismatch";
            require span (equal_ty (Substitute.erase_regions target) ended.given_back_meta.ty)
              "ended ignored mutable loan metadata type mismatch"
        | _ -> reject span "ended ignored mutable loan is not a native mutable reference");
        (* The concrete value is historical synthesis data, not a current
           borrow/loan occurrence. Validate its own type without live lookups. *)
        (Invariants.check_typing_invariant_visitor span ctx false)#visit_tvalue None
          ended.given_back_meta;
        slots := { path = path @ ["given_back_metadata"]; level;
                   role = "given-back-concrete-metadata"; ty = ended.given_back_meta.ty } :: !slots;
        avalue (path @ ["child"]) level ended.child;
        avalue (path @ ["given_back"]) (level + 1) ended.given_back
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
    | ALoan (AIgnoredMutLoan (Some bid,child)) ->
        check_tracked_ignored_mut_loan ~allow_marked span ctx owner level bid v.ty child.ty;
        polarity level false;
        avalue (path @ ["child"]) level child
    | ALoan (AIgnoredMutLoan (None,child)) ->
        polarity level false;
        avalue (path @ ["child"]) level child
    | AIgnored (Some _) | ABorrow _ | ALoan _ ->
        let metadata = match v.value with
          | AIgnored (Some value) -> "\nignored metadata: "
              ^ InterpUtils.tvalue_to_string ctx value
              ^ " : " ^ InterpUtils.ty_to_string ctx value.ty
          | _ -> "" in
        reject span ("concrete, tracked, or unsupported A wrapper at "
          ^ String.concat "/" path ^ " level=" ^ string_of_int level ^ ": "
          ^ InterpUtils.tavalue_to_string ~with_ended:true ctx v ^ metadata
          ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner)
  in
  try
    List.iteri (fun i v ->
      polarities := [];
      avalue ["avalue";string_of_int i] 0 v) owner.avalues;
    (* Call the visitor directly: opt_type_check_abs and the Config.sanity_checks
       switch are deliberately NOT used. This supplements, not replaces, the
       explicit own-history-type and metadata checks above. *)
    current_value := None;
    (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None owner;
    {owner; slots=List.rev !slots}
  with error ->
    let backtrace=Printexc.get_raw_backtrace () in
    let leaf=match !current_value with
      | Some(path,level,value) ->
          "at " ^ String.concat "/" path ^ " level=" ^ string_of_int level
          ^ "\noriginal typed value: " ^ show_tavalue value
      | None -> "at final native owner typing check" in
    Printf.eprintf "SHARED_PACKET_SIGNATURE_REJECTED %s\noriginal owner:\n%s\n%!"
      leaf (InterpUtils.abs_to_string span ~with_ended:true ctx owner);
    (* Keep the original guard, exception, source location, and backtrace. *)
    Printexc.raise_with_backtrace error backtrace
