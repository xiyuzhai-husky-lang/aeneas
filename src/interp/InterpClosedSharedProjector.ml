(** Analysis-only native return of a closed shared projection within or across owners.
    Sublevels and regions stay live. All changed A nodes come from the ordinary
    return/end operations, while original continuations and metadata survive. *)
open Types
open Values
open Contexts
module P = InterpPacketInterface
module C = InterpExternalPermissions
module Existing = InterpClosedSharedComponent
module Preserve = InterpRecordedSharedLeafPreservation

let require span condition message =
  [%cassert] span condition ("Closed shared projector: " ^ message)

type edge = {
  loan_owner : abs; loan_root : tavalue; loan : aproj_loans;
  borrow_owner : abs; borrow_root : tavalue; borrow_value : tavalue;
  borrow : aproj_borrows; marker : proj_marker;
}

let eligible fixed_aids (owner:abs) =
  owner.can_end && AbsId.Set.is_empty owner.parents
  && AbsLevelSet.is_empty owner.ended_subabs
  && not (AbsId.Set.mem owner.abs_id fixed_aids)

let choose _span (ctx:eval_ctx) fixed_aids =
  let rec current_frame = function
    | [] | EFrame::_ -> []
    | EAbs owner::rest when eligible fixed_aids owner -> owner::current_frame rest
    | _::rest -> current_frame rest in
  let owners=current_frame ctx.env in
  List.find_map (fun (loan_owner:abs) ->
    List.find_map (fun (loan_root:tavalue) -> match loan_root.value with
      | ASymbolic ((PLeft|PRight as marker), AProjLoans ({consumed=[];borrows=[];_} as loan)) ->
          List.find_map (fun (borrow_owner:abs) ->
            List.find_map (fun (borrow_root:tavalue) -> match borrow_root.value with
              | ALoan (AEndedIgnoredMutLoan ended) when Existing.inert ended.child ->
                  (match ended.given_back.value with
                  | ASymbolic (pm,AProjBorrows ({loans=[];_} as borrow))
                    when pm=marker && borrow.proj.sv_id=loan.proj.sv_id
                      && equal_ty
                        (InterpBorrowsCore.normalize_proj_ty loan_owner.regions.owned loan.proj.proj_ty)
                        (InterpBorrowsCore.normalize_proj_ty borrow_owner.regions.owned borrow.proj.proj_ty) ->
                      Some {loan_owner;loan_root;loan;borrow_owner;borrow_root;
                        borrow_value=ended.given_back;borrow;marker}
                  | _ -> None)
              | _ -> None) borrow_owner.avalues) owners
      | _ -> None) loan_owner.avalues) owners

(** The identity bridge retains only ignored E leaves and ended ignored
    wrappers. No call, live projector, variable or operative mutable interface
    is hidden by this case. The original E tree is still supplied to native
    return and must be unchanged afterward, including all opaque captures.
    EIgnored metadata may be read under other translation filters: this check
    never licenses deleting it or treating arbitrary ignored data as empty. *)
let inert_cont span (ctx:eval_ctx) (owner:abs) =
  let rec ignored (value:tevalue) =
    not (TypesUtils.ty_has_mut_borrow_for_region_in_set
      ctx.type_ctx.type_infos owner.regions.owned value.ty)
    && match value.value with
    | EIgnored _ -> true
    | EBorrow (EEndedIgnoredMutBorrow ended) -> ignored ended.child && ignored ended.given_back
    | ELoan (EEndedIgnoredMutLoan ended) -> ignored ended.child && ignored ended.given_back
    | _ -> false in
  let inert value =
    let levels=ref (AbsLevelSet.singleton 0) in
    let visitor=object
      inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
      method incr_level level=level+1
      method! visit_tevalue level value =
        levels:=AbsLevelSet.add level !levels;
        super#visit_tevalue level value
    end in
    visitor#visit_tevalue 0 value;
    ignored value && AbsLevelSet.for_all (fun level ->
      match SymbolicToPureAbs.compute_tevalue_proj_kind span ctx.type_ctx.type_infos
          owner.regions.owned level 0 value with
      | SymbolicToPureValues.BorrowProj SymbolicToPureValues.BMut
      | SymbolicToPureValues.LoanProj SymbolicToPureValues.BMut -> false
      | _ -> true) !levels in
  match owner.cont with
  | None -> true
  | Some {input=Some input;output=Some output} -> inert input && inert output
  | _ -> false

let check_closed span (ctx:eval_ctx) (edge:edge) =
  let owners=List.filter_map (function EAbs owner->Some owner|_->None) ctx.env in
  List.iter (fun (owner:abs) ->
    require span (List.length (List.filter (fun (a:abs)->a.abs_id=owner.abs_id) owners)=1)
      "selected owner is not unique";
    ignore (InterpSharedPacketSignature.check ~allow_marked:true span ctx owner);
    require span (inert_cont span ctx owner)
      ("selected owner has an operative continuation: " ^ show_abs owner))
    [edge.loan_owner;edge.borrow_owner];
  let sid=edge.loan.proj.sv_id in
  let shared_lookup=InterpSharedPacketSignature.lookup_retained_shared_value span ctx in
  let occurrences,runtime,issues=C.inventory ~shared_lookup span ctx.env
      (SymbolicValueId.Set.singleton sid) in
  require span (issues=[]) ("incomplete current inventory: " ^ String.concat "; " issues);
  require span (runtime=[]) "selected SID has a current concrete carrier";
  let selected=List.filter (fun (o:C.occurrence)->o.sid=sid) occurrences in
  require span (List.length selected=2 && List.for_all (fun (o:C.occurrence) ->
    o.marker=edge.marker && match o.origin with
    | C.Packet (AProjLoans p) -> o.owner==edge.loan_owner && p==edge.loan && o.level=0
    | C.Packet (AProjBorrows p) -> o.owner==edge.borrow_owner && p==edge.borrow && o.level=1
    | _ -> false) selected) "SID has another current permission or a different native level";
  List.iter (fun ((owner:abs),ty) ->
    require span (not (TypesUtils.ty_has_mut_borrow_for_region_in_set
      ctx.type_ctx.type_infos owner.regions.owned ty)) "selected projection owns a mutable borrow")
    [edge.loan_owner,edge.loan.proj.proj_ty;edge.borrow_owner,edge.borrow.proj.proj_ty];
  (* The exact inert E case above has no selected live projection; its ignored
     metadata is preserved and checked by the native-result comparison below.
     All other current E interfaces/captures retain the existing strict check. *)
  let boundary_owners=List.map (fun (owner:abs) ->
    if owner==edge.loan_owner || owner==edge.borrow_owner then {owner with cont=None}
    else owner) owners in
  ignore (InterpPacketMerge.check_child_e_boundary ~current_env:ctx.env span (P.context_of_eval ctx) boundary_owners sid)

let apply config span (ctx:eval_ctx) (edge:edge) =
  check_closed span ctx edge;
  let plain_loan={edge.loan_root with value=ASymbolic(PNone,AProjLoans edge.loan)}
  and plain_borrow={edge.borrow_value with value=ASymbolic(PNone,AProjBorrows edge.borrow)} in
  let same_owner=edge.loan_owner==edge.borrow_owner in
  let plain_borrow_root=Existing.replace
    [edge.borrow_value,plain_borrow] edge.borrow_root in
  let view_loan={edge.loan_owner with
    avalues=if same_owner then [plain_loan;plain_borrow_root] else [plain_loan]}
  and view_borrow={edge.borrow_owner with avalues=[plain_borrow_root]} in
  let view={ctx with env=if same_owner then [EAbs view_loan]
    else [EAbs view_loan;EAbs view_borrow]} in
  let native=InterpBorrows.return_analysis_sublevel_borrows ~allow_unchanged_cont:true
      config span edge.borrow_owner.abs_id 1 view in
  let native=InterpBorrows.end_unblocked_proj_loans span edge.loan_owner.abs_id
      edge.loan_owner.regions.owned edge.loan.proj native in
  require span (Existing.same_context_except_env view native)
    "native return changed regions or non-environment context";
  let loan_owner=ctx_lookup_abs native edge.loan_owner.abs_id
  and borrow_owner=ctx_lookup_abs native edge.borrow_owner.abs_id in
  let loan_values,borrow_values=if same_owner then
      match loan_owner.avalues with
      | [loan;borrow] -> [loan],[borrow]
      | _ -> [%craise] span "Closed shared projector: unexpected internal native roots"
    else loan_owner.avalues,borrow_owner.avalues in
  let ended_loan,ended_borrow=match loan_values,borrow_values with
    | [{value=ASymbolic(PNone,AEndedProjLoans loan);_}],
      [{value=ALoan(AEndedIgnoredMutLoan {given_back={value=ASymbolic(PNone,AEndedProjBorrows borrow);_};_});_}] ->
        loan,borrow
    | _ -> [%craise] span "Closed shared projector: unexpected native result shape" in
  let returned=ended_borrow.mvalues.given_back in
  require span (ended_borrow.mvalues.consumed=edge.borrow.proj.sv_id
    && returned.sv_id<>edge.borrow.proj.sv_id && ended_borrow.loans=[]
    && equal_ty returned.sv_ty edge.borrow.proj.proj_ty
    && equal_ty ended_borrow.proj_ty edge.borrow.proj.proj_ty)
    "native returned-borrow metadata changed its original full projection";
  require span (ended_loan.proj=edge.loan.proj.sv_id && ended_loan.borrows=[]
    && equal_ty ended_loan.proj_ty edge.loan.proj.proj_ty
    && match ended_loan.consumed with
       | [metadata,AEmpty] -> metadata.sv_id=returned.sv_id
           && equal_ty metadata.proj_ty edge.loan.proj.proj_ty
       | _ -> false) "native loan did not receive precisely the returned shared value";
  let replacements=[
    edge.loan_root,{edge.loan_root with value=ASymbolic(PNone,AEndedProjLoans ended_loan)};
    edge.borrow_value,{edge.borrow_value with value=ASymbolic(PNone,AEndedProjBorrows ended_borrow)}] in
  let expected_loan={edge.loan_owner with avalues=List.map (Existing.replace replacements)
    (if same_owner then [edge.loan_root;edge.borrow_root] else [edge.loan_root])}
  and expected_borrow={edge.borrow_owner with avalues=List.map (Existing.replace replacements) [edge.borrow_root]} in
  let expected_env=if same_owner then [EAbs expected_loan]
    else [EAbs expected_loan;EAbs expected_borrow] in
  require span (Preserve.same_env expected_env native.env)
    "native operation changed an unselected value, lifetime state, continuation or opaque metadata";
  let committed={ctx with env=List.map (function
    | EAbs owner when owner==edge.loan_owner || owner==edge.borrow_owner ->
        EAbs {owner with avalues=List.map (Existing.replace replacements) owner.avalues}
    | entry -> entry) ctx.env} in
  Invariants.check_invariants
    ~shared_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_shared_type_for_typing span committed)
    ~mut_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_mut_borrow_type span committed)
    span committed;
  Printf.eprintf "CLOSED_SHARED_PROJECTOR_RETURN loan_owner=%s borrow_owner=%s sid=%s\n%!"
    (AbsId.to_string edge.loan_owner.abs_id) (AbsId.to_string edge.borrow_owner.abs_id)
    (SymbolicValueId.to_string edge.loan.proj.sv_id);
  committed

let retire config span ~with_abs_conts ~recording ~fixed_aids ctx =
  if with_abs_conts || recording || config.mode<>SymbolicMode then ctx
  else
    let rec run ctx=match choose span ctx fixed_aids with
      | None->ctx | Some edge->run (apply config span ctx edge) in
    run ctx
