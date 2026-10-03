(** Typed recording of one closed right-side shared component. Projection
    preserves its four endpoint identities but can shift root positions. Each
    execution rechecks the complete original environment and uses the native
    return/end operations; no saved continuation is synthesized or replaced. *)
open Types
open Values
open Contexts
module Existing = InterpClosedSharedComponent
module Leaf = InterpRecordedSharedLeaf
module P = InterpPacketInterface

let require span b message =
  [%cassert] span b ("Recorded shared component: " ^ message)

type endpoint = {full_type:ty; mask:ty; ended:RegionId.Set.t}
type action = {
  recorded_owner:abs_id;
  origin_owner:abs_id;
  sid:symbolic_value_id;
  loan_id:loan_id;
  shared_id:shared_borrow_id;
  endpoints:endpoint list;
}

let endpoint_types (c:Existing.component) =
  [c.borrow.proj.proj_ty;c.loan.proj.proj_ty;
   c.concrete.loan_value.ty;c.concrete.borrow_value.ty]

let describe ctx (c:Existing.component) =
  List.map (fun ty ->
    let view=P.view_type (P.context_of_eval ctx) c.owner ty in
    {full_type=view.full;mask=view.normalized;ended=view.ended_regions}) (endpoint_types c)

let matches ctx action (c:Existing.component) =
  c.loan.proj.sv_id=action.sid && c.borrow.proj.sv_id=action.sid
  && c.concrete.loan_id=action.loan_id && c.concrete.shared_id=action.shared_id
  && List.for_all2 (fun expected actual ->
    equal_ty expected.full_type actual.full_type && equal_ty expected.mask actual.mask
    && RegionId.Set.equal expected.ended actual.ended) action.endpoints (describe ctx c)

let validate_owner span ctx fixed_aids (owner:abs) =
  require span (owner.kind=WithCont && owner.can_end && Option.is_some owner.cont
    && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs
    && not (AbsId.Set.mem owner.abs_id fixed_aids))
    "requires an independent live synthesis owner";
  require span (Leaf.current_owner span ctx owner.abs_id==owner)
    "selected owner is not the original current-frame object"

let plan span ~original_joined ~chronological_merges ~fixed_aids ctx (c:Existing.component) =
  require span (Leaf.enabled () && c.marker=PRight) "requires enabled right component";
  validate_owner span ctx fixed_aids c.owner;
  let preliminary={recorded_owner=c.owner.abs_id;origin_owner=c.owner.abs_id;
    sid=c.loan.proj.sv_id;loan_id=c.concrete.loan_id;shared_id=c.concrete.shared_id;
    endpoints=describe ctx c} in
  let lineage=Leaf.origins span original_joined chronological_merges c.owner.abs_id in
  let candidates=List.filter_map (fun aid ->
    let owner=Leaf.current_owner span original_joined aid in
    match Existing.choose ~marker:PRight owner with
    | Some original when matches original_joined preliminary original -> Some owner
    | _ -> None) (AbsId.Set.elements lineage) in
  require span (List.length candidates=1)
    "no unique complete original right component in merge lineage";
  {preliminary with origin_owner=(List.hd candidates).abs_id}

let apply config span ~marker ~fixed_aids action owner ctx =
  require span (Leaf.enabled () && config.mode=SymbolicMode)
    "requires the symbolic recorded-shared path";
  validate_owner span ctx fixed_aids owner;
  let component=match Existing.choose ~marker owner with
    | Some c when matches ctx action c -> c
    | _ -> [%craise] span "Recorded shared component: endpoint identity, full type or mask changed" in
  let result=
    try Existing.apply ~allow_unchanged_cont:true config span ctx component
    with error ->
      let backtrace=Printexc.get_raw_backtrace () in
      Printf.eprintf "RECORDED_SHARED_COMPONENT_NATIVE_REJECTED owner=%s sid=%s marker=%s\n%s\n%!"
        (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string action.sid)
        (show_proj_marker marker) (InterpUtils.abs_to_string span ~with_ended:true ctx owner);
      Printexc.raise_with_backtrace error backtrace in
  Invariants.check_invariants
    ~shared_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_shared_type_for_typing span result)
    ~mut_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_mut_borrow_type span result)
    span result;
  result

let apply_planned config span ~fixed_aids action ctx =
  let owner=Leaf.current_owner span ctx action.recorded_owner in
  let ctx=apply config span ~marker:PRight ~fixed_aids action owner ctx in
  Printf.eprintf "RECORDED_SHARED_COMPONENT_PLANNED owner=%s sid=%s loan=%s origin=%s\n%!"
    (AbsId.to_string action.recorded_owner) (SymbolicValueId.to_string action.sid)
    (BorrowId.to_string action.loan_id) (AbsId.to_string action.origin_owner);
  ctx

let replay config span ~resolve_owner ~fixed_aids action ctx =
  let owner=Leaf.current_owner span ctx (resolve_owner action.recorded_owner) in
  let ctx=apply config span ~marker:PNone ~fixed_aids action owner ctx in
  Printf.eprintf "RECORDED_SHARED_COMPONENT_REPLAYED recorded=%s owner=%s sid=%s loan=%s\n%!"
    (AbsId.to_string action.recorded_owner) (AbsId.to_string owner.abs_id)
    (SymbolicValueId.to_string action.sid) (BorrowId.to_string action.loan_id);
  ctx
