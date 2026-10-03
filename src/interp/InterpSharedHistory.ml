(** Read-only native interface checks shared by analysis and projected replay.
    No context or permission is changed by these predicates. *)
open Values
open Contexts

(** A complete ended tree can be absent from the current permission state while
    still carrying a Pure interface. Check these two facts separately: this
    structural predicate forbids every current permission, while the native
    projection-kind classifier below checks every original sub-abstraction. *)
let rec permission_free_history span ctx (value : tavalue) =
  let recur = permission_free_history span ctx in
  match value.value with
  | AIgnored _ | ASymbolic (PNone,AEmpty) -> true
  | AAdt adt -> List.for_all recur adt.fields
  | ABorrow AEndedSharedBorrow -> true
  | ALoan (AEndedSharedLoan (shared,child)) ->
      ValuesUtils.is_aignored child.value
      && not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared)
  | ALoan (AEndedIgnoredMutLoan ended) -> recur ended.child && recur ended.given_back
  | ASymbolic (PNone,AEndedProjBorrows ended) -> ended.loans=[]
  | ASymbolic (PNone,AEndedProjLoans ended) ->
      List.for_all (fun (_,child) -> child=AEmpty) (ended.consumed @ ended.borrows)
  | _ -> false

let empty_native_interface span (ctx : eval_ctx) (owner : abs) value =
  let levels=ref (AbsLevelSet.singleton 0) in
  let visitor=object
    inherit [_] InterpBorrowsCore.iter_tavalue_with_levels as super
    method incr_level level = level+1
    method! visit_tavalue level value =
      levels:=AbsLevelSet.add level !levels;
      super#visit_tavalue level value
    method! visit_aproj level proj =
      levels:=AbsLevelSet.add level !levels;
      super#visit_aproj level proj
  end in
  visitor#visit_tavalue 0 value;
  AbsLevelSet.for_all (fun level ->
    match SymbolicToPureValues.compute_tavalue_proj_kind span
      ctx.type_ctx.type_infos owner.regions.owned level 0 value with
    | SymbolicToPureValues.BorrowProj SymbolicToPureValues.BMut | SymbolicToPureValues.LoanProj SymbolicToPureValues.BMut -> false
    | SymbolicToPureValues.BorrowProj SymbolicToPureValues.BShared
    | SymbolicToPureValues.LoanProj SymbolicToPureValues.BShared | SymbolicToPureValues.UnknownProj -> true) !levels


(** Read-only comparison for an unchanged historical interface. Native mappers
    can rebuild the metadata records while preserving every field. Ordinary
    Values equality ignores those fields, so inspect the complete carriers
    explicitly; saved environments still require the same original object.
    This never replaces a context node and is intentionally separate from the
    stricter physical checks used to restore continuations after native steps. *)
let same_complete_value left right =
  let module P=InterpRecordedSharedLeafPreservation in
  let same_payload left right=match left,right with
    | P.CapturedEnv left,P.CapturedEnv right -> left==right
    | P.MetaValue left,P.MetaValue right -> equal_tvalue left right
    | P.MetaSymbolic left,P.MetaSymbolic right -> equal_symbolic_value left right
    | P.ConsumedSymbolic left,P.ConsumedSymbolic right ->
        left.sv_id=right.sv_id && Types.equal_ty left.proj_ty right.proj_ty
    | P.GivenBackSymbolic left,P.GivenBackSymbolic right ->
        left.sv_id=right.sv_id && Types.equal_ty left.proj_ty right.proj_ty
    | P.EndedProjectionBorrow left,P.EndedProjectionBorrow right ->
        left.consumed=right.consumed && equal_symbolic_value left.given_back right.given_back
    | P.EndedAbstractMutBorrow left,P.EndedAbstractMutBorrow right ->
        left.bid=right.bid && equal_symbolic_value left.given_back right.given_back
    | P.EndedExpressionMutBorrow left,P.EndedExpressionMutBorrow right ->
        left.bid=right.bid && equal_symbolic_value left.given_back right.given_back
    | _ -> false in
  let left_meta=P.opaque_tavalue left and right_meta=P.opaque_tavalue right in
  equal_tavalue left right && List.length left_meta=List.length right_meta
  && List.for_all2 same_payload left_meta right_meta
