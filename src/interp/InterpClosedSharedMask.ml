(** Closed, shared-only projection cancellation with unequal owner masks.
    Ordinary shared-loan cancellation omits the matching borrow avalue and
    retains its loan (InterpAbs.merge_abstractions_merge_loan_borrow_pairs).
    Apply that same permission rule to an exact two-part symbolic partition,
    then let native loan ending produce the ended projector. No owner regions,
    continuations, returned symbolic values, or history edges are synthesized. *)
open Types
open Values
open Contexts
module P = InterpPacketInterface
module C = InterpExternalPermissions
module Preserve = InterpRecordedSharedLeafPreservation

let require span condition message =
  [%cassert] span condition ("Closed shared mask: " ^ message)

type borrower = { owner : abs; root : tavalue; proj : aproj_borrows }
type component = {
  loan_owner : abs;
  loan_root : tavalue;
  loan : aproj_loans;
  marker : proj_marker;
  left : borrower;
  right : borrower;
}

let eligible fixed (owner : abs) =
  owner.can_end && owner.cont = None
  && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs
  && not (AbsId.Set.mem owner.abs_id fixed)

let choose fixed (ctx : eval_ctx) =
  let rec current_owners = function
    | [] | EFrame :: _ -> []
    | EAbs owner :: rest when eligible fixed owner -> owner :: current_owners rest
    | _ :: rest -> current_owners rest
  in
  let owners = current_owners ctx.env in
  List.find_map (fun (loan_owner : abs) ->
    List.find_map (fun (loan_root : tavalue) -> match loan_root.value with
      | ASymbolic ((PLeft | PRight as marker),
          AProjLoans ({ consumed = []; borrows = []; _ } as loan)) ->
          let borrowers = List.filter_map (fun (owner : abs) ->
            if owner.abs_id = loan_owner.abs_id then None
            else match owner.avalues with
            | [({ value = ASymbolic (pm,
                AProjBorrows ({ loans = []; _ } as proj)); _ } as root)]
              when pm = marker && proj.proj.sv_id = loan.proj.sv_id ->
                Some { owner; root; proj }
            | _ -> None) owners in
          (match borrowers with
           | [left; right] -> Some { loan_owner; loan_root; loan; marker; left; right }
           | _ -> None)
      | _ -> None) loan_owner.avalues) owners

(** Retain every non-region type field and inspect each original occurrence.
    In particular, one loan lifetime can cover two independent generic borrow
    lifetimes. Canonicalization is a read-only shape comparison, never a type
    substitution in the interpreter context. *)
let shape_and_mask span (ctx : eval_ctx) (owner : abs) ty =
  require span (not (TypesUtils.ty_has_mut_borrows ctx.type_ctx.type_infos ty))
    "mutable reference in selected full type";
  require span (not (TypesUtils.ty_has_nested_borrows (Some span)
      ctx.type_ctx.type_infos ty)) "nested reference in selected full type";
  let mask = ref [] in
  let visitor = object
    inherit [_] map_ty
    method! visit_region () = function
      | RVar (Free rid) ->
          require span (not (RegionId.Set.mem rid ctx.ended_regions))
            "selected type contains an ended region";
          mask := RegionId.Set.mem rid owner.regions.owned :: !mask;
          RVar (Free (RegionId.of_int 0))
      | _ -> [%craise] span "Closed shared mask: selected type has a non-free region"
  end in
  let shape = visitor#visit_ty () ty in
  let mask = List.rev !mask in
  require span (List.exists Fun.id mask) "empty selected ownership mask";
  shape, mask

(** A native input starts with filter=true. ELet and EApp pass that flag
    unchanged (SymbolicToPureAbs.einput_to_texpr). Along exactly those paths,
    EIgnored(Some _) is not read. Hide only the selected, fully typed symbolic
    metadata from the child-deletion admission check; native composition still
    receives the complete original continuation and captured environment. *)
let filtered_capture_view span c (owner : abs) =
  let rec input (value : tevalue) =
    let changed = match value.value with
    | EIgnored (Some (_, ({value=VSymbolic symbolic;_} as captured)))
      when symbolic.sv_id=c.loan.proj.sv_id ->
        require span (equal_ty symbolic.sv_ty c.loan.proj.proj_ty
          && equal_ty captured.ty (Substitute.erase_regions value.ty)
          && equal_ty captured.ty (Substitute.erase_regions symbolic.sv_ty))
          "filtered capture differs from the original selected shared value";
        EIgnored None
    | ELet (owned,pattern,bound,next) ->
        ELet (owned,pattern,input bound,input next)
    | EApp (callee,arguments) -> EApp (callee,List.map (List.map input) arguments)
    | original -> original in
    {value with value=changed} in
  if owner==c.loan_owner || owner==c.left.owner || owner==c.right.owner then
    {owner with cont=Option.map (fun cont ->
      {cont with input=Option.map input cont.input}) owner.cont}
  else owner

let check_closed ?(allow_filtered_captures=false) span (ctx : eval_ctx) c =
  let owners = List.filter_map (function EAbs owner -> Some owner | _ -> None) ctx.env in
  let selected_owners = [c.loan_owner; c.left.owner; c.right.owner] in
  List.iter (fun (owner : abs) ->
    require span (List.length (List.filter (fun (other : abs) ->
      other.abs_id = owner.abs_id) owners) = 1) "selected owner is not unique";
    Invariants.opt_type_check_abs span ctx owner) selected_owners;
  require span (equal_ty c.loan_root.ty c.loan.proj.proj_ty
    && equal_ty c.left.root.ty c.left.proj.proj.proj_ty
    && equal_ty c.right.root.ty c.right.proj.proj.proj_ty)
    "selected wrapper and full projector types differ";
  let loan_shape, loan_mask = shape_and_mask span ctx c.loan_owner c.loan.proj.proj_ty
  and left_shape, left_mask = shape_and_mask span ctx c.left.owner c.left.proj.proj.proj_ty
  and right_shape, right_mask = shape_and_mask span ctx c.right.owner c.right.proj.proj.proj_ty in
  require span (equal_ty loan_shape left_shape && equal_ty loan_shape right_shape
    && List.length loan_mask = List.length left_mask
    && List.length loan_mask = List.length right_mask)
    "full positional type shapes differ";
  require span (List.for_all2 (fun left right -> not (left && right)) left_mask right_mask)
    "borrow masks overlap";
  require span (List.for_all2 (=) loan_mask (List.map2 (||) left_mask right_mask))
    "borrow masks do not exactly partition the loan";
  List.iter (fun b ->
    require span (InterpBorrowsCore.projection_contains span ctx
      c.loan_owner.regions.owned c.loan.proj.proj_ty
      b.owner.regions.owned b.proj.proj.proj_ty)
      "native loan containment check failed") [c.left; c.right];
  let sid = c.loan.proj.sv_id in
  let shared_lookup = InterpSharedPacketSignature.lookup_retained_shared_value span ctx in
  let all, runtime, issues = C.inventory ~shared_lookup span ctx.env
    (SymbolicValueId.Set.singleton sid) in
  require span (issues = []) ("incomplete current inventory: " ^ String.concat "; " issues);
  require span (runtime = []) "selected SID has a current runtime carrier";
  let occurrences = List.filter (fun (o : C.occurrence) -> o.sid = sid) all in
  require span (List.length occurrences = 3 && List.for_all (fun (o : C.occurrence) ->
    o.marker = c.marker && o.level = 0 && match o.origin with
    | C.Packet (AProjLoans loan) -> o.owner == c.loan_owner && loan == c.loan
    | C.Packet (AProjBorrows proj) ->
        (o.owner == c.left.owner && proj == c.left.proj)
        || (o.owner == c.right.owner && proj == c.right.proj)
    | _ -> false) occurrences)
    "selected SID has an additional current permission or history";
  let boundary_owners = if allow_filtered_captures then
    List.map (filtered_capture_view span c) owners else owners in
  ignore (InterpPacketMerge.check_child_e_boundary ~current_env:ctx.env span (P.context_of_eval ctx) boundary_owners sid)

let check_invariants span ctx =
  (* Current marked branches may still carry the two native copies of one
     shared-borrow ID. Selected closure, native types, union masks and exact
     post-state preservation are checked separately here; global uniqueness
     remains checked at the native completed-collapse boundary. *)
  let marked = List.exists (function
    | EAbs owner -> InterpUtils.abs_has_markers owner
    | EBinding _ | EFrame -> false) ctx.env in
  if not marked then
    Invariants.check_invariants
      ~shared_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_shared_type_for_typing span ctx)
      ~mut_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_mut_borrow_type span ctx)
      span ctx

let apply span (ctx : eval_ctx) c =
  check_closed span ctx c;
  check_invariants span ctx;
  (* This is the ordinary shared cancellation result: omit the two borrow
     roots. The complete loan and both original owner records survive. *)
  let cancelled = { ctx with env = List.map (function
    | EAbs owner when owner == c.left.owner || owner == c.right.owner ->
        EAbs { owner with avalues = [] }
    | entry -> entry) ctx.env } in
  let native = InterpBorrows.end_unblocked_proj_loans span c.loan_owner.abs_id
    c.loan_owner.regions.owned c.loan.proj cancelled in
  let native_owner = ctx_lookup_abs native c.loan_owner.abs_id in
  let ended_root = List.find_map (fun (root : tavalue) -> match root.value with
    | ASymbolic (pm, AEndedProjLoans ended)
      when pm = c.marker && ended.proj = c.loan.proj.sv_id -> Some (root, ended)
    | _ -> None) native_owner.avalues in
  let ended_root, ended = match ended_root with
    | Some value -> value
    | None -> [%craise] span "Closed shared mask: native loan ending produced no selected root" in
  require span (ended.consumed = [] && ended.borrows = []
    && equal_ty ended.proj_ty c.loan.proj.proj_ty
    && equal_ty ended_root.ty c.loan_root.ty)
    "native ending changed the original projection or introduced history";
  let committed = { cancelled with env = List.map (function
    | EAbs owner when owner == c.loan_owner ->
        EAbs { owner with avalues = List.map (fun root ->
          if root == c.loan_root then ended_root else root) owner.avalues }
    | entry -> entry) cancelled.env } in
  require span (InterpClosedSharedComponent.same_context_except_env ctx native
    && Preserve.same_env committed.env native.env)
    "native ending changed an unselected value, lifetime, or historical payload";
  check_invariants span committed;
  if Sys.getenv_opt "AENEAS_TRACE_SHARED_MASK" = Some "1" then
  Printf.eprintf "CLOSED_SHARED_MASK_CANCELLED loan_owner=%s borrow_owners=%s,%s sid=%s\n%!"
    (AbsId.to_string c.loan_owner.abs_id) (AbsId.to_string c.left.owner.abs_id)
    (AbsId.to_string c.right.owner.abs_id) (SymbolicValueId.to_string c.loan.proj.sv_id);
  committed

let retire config span ~with_abs_conts ~recording ~fixed_aids ctx =
  if with_abs_conts || recording || config.mode <> SymbolicMode then ctx
  else
    let rec run ctx = match choose fixed_aids ctx with
      | None -> ctx | Some component -> run (apply span ctx component) in
    run ctx

(** A partial shared projection can also form a cycle with its source owner:
    the source owns the complete loan and one slice of the borrow, while the
    other borrower still exports unrelated shared loans. Discharging those
    borrows must join the two owners, so those outputs retain their dependency
    on the original source. Do this before ordinary concrete merging would
    capture a non-owned region in a retained projector. *)
let choose_cycle ?(with_abs_conts=false) ?(marker=None) fixed (ctx : eval_ctx) =
  let eligible_cycle (owner : abs) =
    if with_abs_conts then owner.can_end && Option.is_some owner.cont
      && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs
      && not (AbsId.Set.mem owner.abs_id fixed)
    else eligible fixed owner in
  let rec current_owners = function
    | [] | EFrame :: _ -> []
    | EAbs owner :: rest when eligible_cycle owner -> owner :: current_owners rest
    | _ :: rest -> current_owners rest in
  let owners = current_owners ctx.env in
  List.find_map (fun (loan_owner : abs) ->
    List.find_map (fun (loan_root : tavalue) -> match loan_root.value with
      | ASymbolic (pm, AProjLoans ({ consumed = []; borrows = []; _ } as loan))
        when (match marker with Some expected -> pm=expected
          | None -> pm=PLeft || pm=PRight) ->
          let marker=pm in
          let borrowers = List.concat_map (fun (owner : abs) ->
            List.filter_map (fun (root : tavalue) -> match root.value with
              | ASymbolic (pm, AProjBorrows ({ loans = []; _ } as proj))
                when pm = marker && proj.proj.sv_id = loan.proj.sv_id ->
                  Some {owner;root;proj}
              | _ -> None) owner.avalues) owners in
          (match borrowers with
          | [left;right] when left.owner.abs_id <> right.owner.abs_id
              && (left.owner == loan_owner || right.owner == loan_owner) ->
              Some {loan_owner;loan_root;loan;marker;left;right}
          | _ -> None)
      | _ -> None) loan_owner.avalues) owners

let apply_cycle ?(with_abs_conts=false) span ~abs_kind ~merge_funs (ctx : eval_ctx) c =
  require span (not with_abs_conts || (c.marker=PNone
    && Option.is_some c.loan_owner.cont && Option.is_some c.left.owner.cont
    && Option.is_some c.right.owner.cont))
    "synthesis cycle requires original unmarked continuations";
  check_closed ~allow_filtered_captures:with_abs_conts span ctx c;
  let other = if c.left.owner == c.loan_owner then c.right.owner else c.left.owner in
  let selected_ids = AbsId.Set.of_list [c.loan_owner.abs_id;other.abs_id] in
  List.iter (function
    | EAbs owner when not (AbsId.Set.mem owner.abs_id selected_ids) ->
        require span (AbsId.Set.is_empty (AbsId.Set.inter owner.parents selected_ids))
          "selected cycle has an external child abstraction"
    | _ -> ()) ctx.env;
  let plain_shared_root (owner : abs) (root : tavalue) = match root.value with
    | ASymbolic (_, AProjLoans {consumed=[];borrows=[];_})
    | ASymbolic (_, AProjBorrows {loans=[];_}) ->
        not (TypesUtils.ty_has_mut_borrows ctx.type_ctx.type_infos root.ty)
        && not (TypesUtils.ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos root.ty)
    | ABorrow (ASharedBorrow _) ->
        (match root.ty with
        | TRef (_,referent,RShared)
          when not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent) ->
            (* This unselected permission survives unchanged. Reuse the strict
               native loan/type/owned-level checks; the exact-result comparison
               below forbids the merge from deleting or relabelling it. *)
            InterpSharedPacketSignature.check_retained_shared_borrow
              ~allow_marked:true span ctx owner 0 root;
            true
        | _ -> false)
    | ALoan (ASharedLoan (_,_,value,child)) ->
        ValuesUtils.is_aignored child.value
        && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos value.ty)
        && not (InterpUtils.value_has_loans_or_borrows (Some span) ctx value.value)
    | _ -> false in
  List.iter (fun (owner : abs) ->
    (match List.find_opt (fun root -> not (plain_shared_root owner root)) owner.avalues with
    | None -> ()
    | Some root ->
        Printf.eprintf
          "CLOSED_SHARED_MASK_CYCLE_UNSUPPORTED_ROOT selected_sid=%s\nroot=%s\nloan owner:\n%s\nother owner:\n%s\n%!"
          (SymbolicValueId.to_string c.loan.proj.sv_id) (show_tavalue root)
          (InterpUtils.abs_to_string span ~with_ended:true ctx c.loan_owner)
          (InterpUtils.abs_to_string span ~with_ended:true ctx other));
    require span (List.for_all (plain_shared_root owner) owner.avalues)
      "cycle owner has a nested, mutable, historical or unsupported root")
    [c.loan_owner;other];
  check_invariants span ctx;
  let remove_borrows (owner : abs) = {owner with avalues=List.filter (fun root ->
    root != c.left.root && root != c.right.root) owner.avalues} in
  let left = remove_borrows c.loan_owner and right = remove_borrows other in
  let owned = RegionId.Set.union left.regions.owned right.regions.owned in
  let packet_ctx = P.context_of_eval ctx in
  List.iter (fun owner ->
    (* Original E inputs are composed by native merge_abs_conts, which wraps
       each continuation in ELet with that owner's original region scope.
       The current A interface instead uses the new union directly. *)
    let current_owner=if with_abs_conts then {owner with cont=None} else owner in
    try ignore (InterpPacketMerge.check_union_masks packet_ctx
      (P.describe_owner packet_ctx current_owner) owned)
    with InterpPacketMerge.Unsupported reason ->
      [%craise] span ("Closed shared mask: cycle union: " ^ reason)) [left;right];
  (* This is the existing native abstraction merge, without the additional
     global region-coalescing approximation in merge_into_first_abstraction.
     Its result must preserve every residual original root in order. *)
  let merged = InterpAbs.merge_abstractions span abs_kind ~can_end:true
    merge_funs ~with_abs_conts ctx left right in
  let expected_roots = left.avalues @ right.avalues in
  require span (Option.is_some merged.cont=with_abs_conts && merged.can_end && merged.kind=abs_kind
    && AbsId.Set.is_empty merged.parents && AbsLevelSet.is_empty merged.ended_subabs
    && RegionId.Set.equal merged.regions.owned owned
    && List.length merged.avalues = List.length expected_roots
    && List.for_all2 Preserve.same_tavalue merged.avalues expected_roots)
    "native cycle merge changed an unselected root or lifetime";
  let merged = {merged with avalues=expected_roots} in
  let joined = fst (ctx_subst_abs span ctx c.loan_owner.abs_id merged) in
  let joined = fst (ctx_remove_abs span joined other.abs_id) in
  let native = InterpBorrows.end_unblocked_proj_loans span merged.abs_id
    owned c.loan.proj joined in
  let native_owner = ctx_lookup_abs native merged.abs_id in
  let ended_root = List.find_map (fun (root : tavalue) -> match root.value with
    | ASymbolic (pm,AEndedProjLoans ended)
      when pm=c.marker && ended.proj=c.loan.proj.sv_id -> Some (root,ended)
    | _ -> None) native_owner.avalues in
  let ended_root,ended = match ended_root with
    | Some result -> result
    | None -> [%craise] span "Closed shared mask: native cycle ending produced no selected root" in
  require span (ended.consumed=[] && ended.borrows=[]
    && equal_ty ended.proj_ty c.loan.proj.proj_ty
    && equal_ty ended_root.ty c.loan_root.ty)
    "native cycle ending changed the selected projection or introduced history";
  let committed_owner = {merged with avalues=List.map (fun root ->
    if root == c.loan_root then ended_root else root) expected_roots} in
  let committed = fst (ctx_subst_abs span joined merged.abs_id committed_owner) in
  require span (InterpClosedSharedComponent.same_context_except_env ctx native
    && Preserve.same_env committed.env native.env)
    "native cycle ending changed an external value, lifetime or historical payload";
  (* Finish the same native top-root cleanup as the ordinary simplifier, but
     only for the loan just ended above. Its empty history has no remaining
     permission or Pure interface. Every other original root and continuation
     stays exact, so a subsequent cycle sees the current interface directly. *)
  require span (InterpBorrows.ended_shared_loan_is_eliminable span committed ended_root)
    "native ended cycle root is not eliminable";
  let cleaned_roots = List.filter (fun root -> root != ended_root) committed_owner.avalues in
  require span (List.length cleaned_roots + 1 = List.length committed_owner.avalues)
    "native ended cycle cleanup did not select exactly one root";
  let committed = fst (ctx_subst_abs span committed merged.abs_id
    {committed_owner with avalues=cleaned_roots}) in
  check_invariants span committed;
  if Sys.getenv_opt "AENEAS_TRACE_SHARED_MASK" = Some "1" then
  Printf.eprintf "CLOSED_SHARED_MASK_CYCLE_MERGED owners=%s,%s result=%s sid=%s\n%!"
    (AbsId.to_string c.loan_owner.abs_id) (AbsId.to_string other.abs_id)
    (AbsId.to_string merged.abs_id) (SymbolicValueId.to_string c.loan.proj.sv_id);
  committed

let retire_cycles config span ~with_abs_conts ~recording ~fixed_aids ~abs_kind
    ~merge_funs ctx =
  if with_abs_conts || recording || config.mode <> SymbolicMode then ctx
  else let rec run ctx = match choose_cycle fixed_aids ctx with
    | None -> ctx
    | Some component -> run (apply_cycle span ~abs_kind ~merge_funs:(Some merge_funs) ctx component)
  in run ctx


(** Read-only evidence at the original target boundary, before markers and
    merge recording. This never changes the context or runs native ending. *)
let trace_unmarked_cycle span fixed ctx =
  match choose_cycle ~with_abs_conts:true ~marker:(Some PNone) fixed ctx with
  | None -> ()
  | Some c ->
      let other=if c.left.owner==c.loan_owner then c.right.owner else c.left.owner in
      let owners=List.filter_map (function EAbs owner->Some owner|_->None) ctx.env in
      List.iter (fun (owner : abs) ->
        let descriptor=P.describe_owner (P.context_of_eval ctx) owner in
        List.iter (fun (capture : P.capture) ->
          let contains=ref false in
          let visitor=object
            inherit [_] iter_tvalue
            method! visit_symbolic_value_id () sid =
              if sid=c.loan.proj.sv_id then contains:=true
          end in
          visitor#visit_tvalue () capture.value;
          if !contains then
            let constructor=match capture.at.original with
              | P.EValue {value=EValue _;_} -> "EValue"
              | P.EValue {value=EIgnored _;_} -> "EIgnored"
              | _ -> "unexpected" in
            Printf.eprintf "SHARED_MASK_CAPTURE owner=%s path=%s constructor=%s value=%s\n%!"
              (AbsId.to_string owner.abs_id) (String.concat "/" capture.at.path)
              constructor (show_tvalue capture.value)) descriptor.captures) owners;
      let boundary=try
        let checks,_=InterpPacketMerge.check_child_e_boundary ~current_env:ctx.env span
          (P.context_of_eval ctx) owners c.loan.proj.sv_id in
        "accepted checks=" ^ string_of_int checks
      with InterpPacketMerge.Unsupported reason -> "rejected " ^ reason in
      Printf.eprintf "SHARED_MASK_UNMARKED_TARGET sid=%s E=%s\n%s\n%s\n%!"
        (SymbolicValueId.to_string c.loan.proj.sv_id) boundary
        (InterpUtils.abs_to_string span ~with_ended:true ctx c.loan_owner)
        (InterpUtils.abs_to_string span ~with_ended:true ctx other)


(** Apply the shared-only cycle rule to the original synthesis target, before
    joining branches. Native composition preserves the two original scoped
    continuations; the native loan ending is its identity-continuation branch.
    No marked action or replay sequence is bypassed. *)
let retire_target_cycles config span ~fixed_aids ~abs_kind ctx =
  if config.mode <> SymbolicMode then ctx
  else let rec run ctx =
    match choose_cycle ~with_abs_conts:true ~marker:(Some PNone) fixed_aids ctx with
    | None -> ctx
    | Some component ->
        run (apply_cycle ~with_abs_conts:true span ~abs_kind ~merge_funs:None ctx component)
  in run ctx
