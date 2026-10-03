(** Retire a closed concrete shared edge lifted to a top-level loan by native
    decomposition. Only loop analysis is supported: no owner, lifetime, parent,
    or continuation is ended. Native operations determine both changed leaves. *)
open Types
open Values
open Contexts
module P = InterpPacketInterface
module Base = InterpClosedSharedComponent
module Preserve = InterpRecordedSharedLeafPreservation

let require span condition message =
  [%cassert] span condition ("Closed shared concrete edge: " ^ message)

type candidate = {
  owner : abs;
  marker : proj_marker;
  loan_root : tavalue;
  wrapper_root : tavalue;
  borrow_leaf : tavalue;
  loan_id : loan_id;
  shared_id : shared_borrow_id;
  shared_value : tvalue;
  loan_child : tavalue;
}

(** The given-back tree is at native sublevel one. Its only current permission
    must be the selected shared borrow, so returning that sublevel cannot return
    any additional symbolic or concrete permission. *)
let rec borrowed_leaves (value : tavalue) =
  if Base.inert value then Some []
  else match value.value with
  | AAdt adt ->
      let fields = List.map borrowed_leaves adt.fields in
      if List.for_all Option.is_some fields then
        Some (List.concat (List.filter_map Fun.id fields)) else None
  | ABorrow (ASharedBorrow ((PLeft | PRight as marker), bid, sid)) ->
      Some [value, marker, bid, sid]
  | _ -> None

let choose span (ctx : eval_ctx) (owner : abs) =
  List.find_map (fun (wrapper_root : tavalue) ->
    match wrapper_root.value with
    | ALoan (AEndedIgnoredMutLoan ended)
      when Base.permission_free_history span ctx ended.child ->
        (match borrowed_leaves ended.given_back with
        | Some [borrow_leaf, marker, loan_id, shared_id] ->
            let loans = List.filter_map (fun (loan_root : tavalue) ->
              match loan_root.value with
              | ALoan (ASharedLoan (pm, bid, shared_value, loan_child))
                when pm=marker && bid=loan_id ->
                  (match loan_child.value with
                  | AIgnored _ -> Some {owner; marker; loan_root; wrapper_root;
                      borrow_leaf; loan_id; shared_id; shared_value; loan_child}
                  | _ -> None)
              | _ -> None) owner.avalues in
            (match loans with [candidate] -> Some candidate | _ -> None)
        | _ -> None)
    | _ -> None) owner.avalues

(** Inspect the actual captured value, resolving its shared references only in
    its saved environment. The rest of that historical environment is not a
    current permission. Symbolic IDs are deliberately not retired here. *)
let check_captured_ids span bid sid snapshot value =
  let rec walk ancestors seen (value : tvalue) =
    require span (not (List.exists ((==) value) ancestors)) "cyclic captured value";
    let ancestors=value::ancestors in
    let different id = require span (id<>bid) "selected loan ID occurs in captured value" in
    let different_shared id = require span (id<>sid)
      "selected shared-borrow ID occurs in captured value" in
    match value.value with
    | VSymbolic _ | VLiteral _ | VBottom -> ()
    | VAdt adt -> List.iter (walk ancestors seen) adt.fields
    | VLoan (VMutLoan id) -> different id
    | VLoan (VSharedLoan (id,value)) | VBorrow (VMutBorrow (id,value)) ->
        different id; walk ancestors seen value
    | VBorrow (VSharedBorrow (id,shared) | VReservedMutBorrow (id,shared)) ->
        different id; different_shared shared;
        require span (not (BorrowId.Set.mem id seen)) "cyclic captured shared borrow";
        let env = match snapshot with
          | Some env -> env
          | None -> [%craise] span "Closed shared concrete edge: captured borrow has no saved environment" in
        let value=InterpBorrowsCore.lookup_shared_value span env id in
        walk ancestors (BorrowId.Set.add id seen) value
  in walk [] BorrowId.Set.empty value

let check_closed span (ctx : eval_ctx) (c : candidate) =
  let owners=List.filter_map (function EAbs owner -> Some owner | _ -> None) ctx.env in
  require span (List.length (List.filter (fun (owner : abs) -> owner.abs_id=c.owner.abs_id) owners)=1)
    "selected owner is not unique";
  ignore (InterpSharedPacketSignature.check ~allow_marked:true span ctx c.owner);
  let loan=InterpSharedPacketSignature.lookup_retained_shared_value span ctx c.marker c.loan_id in
  require span (loan==c.shared_value) "selected current loan payload differs";
  (* Includes current A and E, runtime carriers, and constant-generic values.
     Opaque metadata is inspected below according to its actual native use. *)
  let borrows=ref 0 and loans=ref 0 and shared=ref 0 in
  let ids=object
    inherit [_] iter_eval_ctx
    method! visit_borrow_id () id = if id=c.loan_id then incr borrows
    method! visit_loan_id () id = if id=c.loan_id then incr loans
    method! visit_shared_borrow_id () id = if id=c.shared_id then incr shared
  end in
  ids#visit_eval_ctx () ctx;
  require span (!borrows=1 && !loans=1 && !shared=1)
    "selected concrete IDs have additional current A/E/runtime occurrences";
  let pc=P.context_of_eval ctx in
  List.iter (fun (owner : abs) ->
    let d=P.describe_owner pc owner in
    List.iter (fun (capture : P.capture) ->
      check_captured_ids span c.loan_id c.shared_id (Some capture.snapshot) capture.value) d.captures;
    List.iter (fun (metadata : P.concrete_metadata) ->
      let unused_ended_ignored = List.exists (fun (node : P.node) ->
        node.surface=P.A && metadata.at.surface=P.A
        && metadata.at.path=node.path@["given_back_meta"]
        && match node.original with
          | P.AValue {value=ALoan (AEndedIgnoredMutLoan ended);_} ->
              ended.given_back_meta==metadata.value
          | _ -> false) d.nodes in
      let unused_root = match metadata.at.surface,metadata.at.path with
        | P.A,["avalue";index;"ignored_meta"] ->
            (match int_of_string_opt index with
            | Some i -> (match List.nth_opt owner.avalues i with
                | Some {value=AIgnored(Some value);_} -> value==metadata.value
                | _ -> false)
            | None -> false)
        | _ -> false in
      (* Native Pure conversion does not read these exact ignored A carriers;
         their original objects are nevertheless retained in the committed tree. *)
      if not (unused_ended_ignored || unused_root) then
        check_captured_ids span c.loan_id c.shared_id None metadata.value) d.concrete_metadata) owners;
  ConstGenericVarId.Map.iter (fun _ value ->
    check_captured_ids span c.loan_id c.shared_id None value) ctx.const_generic_vars_map;
  require span (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx c.shared_value))
    "selected shared referent contains current permissions"

let apply config span (ctx : eval_ctx) (c : candidate) =
  check_closed span ctx c;
  let originals=[c.loan_root;c.wrapper_root] in
  let unmarked=[
    c.loan_root,{c.loan_root with value=ALoan(ASharedLoan(PNone,c.loan_id,c.shared_value,c.loan_child))};
    c.borrow_leaf,{c.borrow_leaf with value=ABorrow(ASharedBorrow(PNone,c.loan_id,c.shared_id))}
  ] in
  (* Complete wrappers and historical data survive in the scoped view. Only
     the two proven closed current endpoints are unmarked for native lookup. *)
  let view_owner={c.owner with avalues=List.map (Base.replace unmarked) originals} in
  let view={ctx with env=[EAbs view_owner]} in
  let native=InterpBorrows.return_analysis_sublevel_borrows config span c.owner.abs_id 1 view in
  let native=InterpBorrows.end_loan_no_synth config span ~snapshots:false c.loan_id native in
  require span (Base.same_context_except_env view native)
    "native operation changed non-environment context";
  let ended=[
    c.loan_root,{c.loan_root with value=ALoan(AEndedSharedLoan(c.shared_value,c.loan_child))};
    c.borrow_leaf,{c.borrow_leaf with value=ABorrow AEndedSharedBorrow}
  ] in
  let expected={c.owner with avalues=List.map (Base.replace ended) originals} in
  require span (Preserve.same_env [EAbs expected] native.env)
    "native result differs from the two exact ended leaves or changed historical metadata";
  (* Commit original siblings and metadata, not the generic native traversal's
     reconstructed objects. There is no region/sublevel ending or live-marker
     erasure in the committed context. *)
  let owner={c.owner with avalues=List.map (Base.replace ended) c.owner.avalues} in
  let committed={ctx with env=List.map (function
    | EAbs old when old==c.owner -> EAbs owner
    | entry -> entry) ctx.env} in
  ignore (InterpSharedPacketSignature.check ~allow_marked:true span committed owner);
  Printf.eprintf "CLOSED_SHARED_CONCRETE_RETIRED owner=%s loan=%s borrow=%s\n%!"
    (AbsId.to_string owner.abs_id) (BorrowId.to_string c.loan_id)
    (SharedBorrowId.to_string c.shared_id);
  committed

let retire config span ~with_abs_conts ~recording ~fixed_aids (ctx : eval_ctx) : eval_ctx =
  if with_abs_conts || recording || config.mode<>SymbolicMode then ctx
  else
    let rec run ctx =
      let rec current_frame = function
        | [] | EFrame::_ -> None
        | EAbs owner::rest ->
            let candidate =
              if owner.can_end && owner.cont=None
                && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs
                && not (AbsId.Set.mem owner.abs_id fixed_aids)
              then choose span ctx owner else None in
            (match candidate with Some candidate -> Some candidate | None -> current_frame rest)
        | _::rest -> current_frame rest in
      match current_frame ctx.env with
      | None -> ctx
      | Some candidate -> run (apply config span ctx candidate)
    in run ctx
