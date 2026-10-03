(** Retire one closed, same-side shared component in a loop-analysis owner.
    The native return/end operations determine every changed value. We retain
    their history metadata, but commit through the original typed trees so all
    unrelated roots, siblings, and historical captures retain their objects.
    This is not abstraction ending: no region or sublevel is marked ended. *)
open Types
open Values
open Contexts
module P = InterpPacketInterface
module C = InterpExternalPermissions
module Preserve = InterpRecordedSharedLeafPreservation

let require span condition message =
  [%cassert] span condition ("Closed shared component: " ^ message)

let inert (v : tavalue) = match v.value with
  | AIgnored _ | ASymbolic (PNone, AEmpty) -> true
  | _ -> false

type concrete_pair = {
  loan_value : tavalue;
  borrow_value : tavalue;
  loan_id : loan_id;
  shared_id : shared_borrow_id;
  shared_value : tvalue;
  loan_child : tavalue;
}

type component = {
  owner : abs;
  marker : proj_marker;
  borrow_root : tavalue;
  borrow_value : tavalue;
  borrow : aproj_borrows;
  loan_root : tavalue;
  loan : aproj_loans;
  concrete_root : tavalue;
  extra_concrete_loan_root : tavalue option;
  concrete : concrete_pair;
}

(** Both sides retain their own ADT projection flag and original full types. *)
let rec concrete_pairs marker (left : tavalue) (right : tavalue) =
  if inert left && inert right then Some []
  else match left.value, right.value with
  | AAdt l, AAdt r when l.variant_id = r.variant_id
      && equal_ty left.ty right.ty && List.length l.fields = List.length r.fields ->
      let pairs = List.map2 (concrete_pairs marker) l.fields r.fields in
      if List.for_all Option.is_some pairs then
        Some (List.concat (List.filter_map Fun.id pairs)) else None
  | ALoan (ASharedLoan (pm, bid, value, child)),
    ABorrow (ASharedBorrow (pm', bid', sid))
    when pm = marker && pm' = marker && bid = bid' && inert child ->
      Some [{loan_value=left; borrow_value=right; loan_id=bid; shared_id=sid;
        shared_value=value; loan_child=child}]
  | _ -> None

(** A lifted native shared loan leaves its historical ended loan in the
    original ADT and keeps the matching live borrow in the returned ADT. Only
    this exact aligned shape is admitted; the old history is never replaced. *)
let rec lifted_borrows marker (left : tavalue) (right : tavalue) =
  if inert left && inert right then Some []
  else match left.value,right.value with
  | AAdt l,AAdt r when l.variant_id=r.variant_id && equal_ty left.ty right.ty
      && List.length l.fields=List.length r.fields ->
      let found=List.map2 (lifted_borrows marker) l.fields r.fields in
      if List.for_all Option.is_some found then
        Some (List.concat (List.filter_map Fun.id found)) else None
  | ALoan (AEndedSharedLoan (_,child)),ABorrow (ASharedBorrow (pm,bid,sid))
      when pm=marker && inert child -> Some [(right,bid,sid)]
  | _ -> None

let concrete_candidate marker (owner : abs) (root : tavalue) (ended : aended_ignored_mut_loan) =
  match concrete_pairs marker ended.child ended.given_back with
  | Some [pair] -> Some (root,None,pair)
  | _ ->
      (match lifted_borrows marker ended.child ended.given_back with
      | Some [(borrow_value,loan_id,shared_id)] ->
          let loans=List.filter_map (fun (loan_value : tavalue) ->
            match loan_value.value with
            | ALoan (ASharedLoan (pm,bid,shared_value,loan_child))
                when pm=marker && bid=loan_id && inert loan_child ->
                Some {loan_value;borrow_value;loan_id;shared_id;shared_value;loan_child}
            | _ -> None) owner.avalues in
          (match loans with
          | [pair] -> Some (root,Some pair.loan_value,pair)
          | _ -> None)
      | _ -> None)

(** Marked analysis components are the default. Replay can explicitly select
    the same closed component after the native right projection removes markers. *)
let choose ?marker (owner : abs) : component option =
  let borrowers = List.filter_map (fun (root : tavalue) ->
    match root.value with
    | ALoan (AEndedIgnoredMutLoan ended) when inert ended.child ->
        (match ended.given_back.value with
        | ASymbolic (pm, AProjBorrows ({loans=[]; _} as borrow))
            when (match marker with
              | None -> pm=PLeft || pm=PRight
              | Some selected -> pm=selected) ->
            Some (root, ended.given_back, pm, borrow)
        | _ -> None)
    | _ -> None) owner.avalues in
  match borrowers with
  | [borrow_root, borrow_value, marker, borrow] ->
      let loans = List.filter_map (fun (root : tavalue) ->
        match root.value with
        | ASymbolic (pm, AProjLoans ({consumed=[];borrows=[];_} as loan))
          when pm=marker && loan.proj.sv_id=borrow.proj.sv_id -> Some (root,loan)
        | _ -> None) owner.avalues in
      let concrete = List.filter_map (fun (root : tavalue) ->
        match root.value with
        | ALoan (AEndedIgnoredMutLoan ended) ->
            concrete_candidate marker owner root ended
        | _ -> None) owner.avalues in
      (match loans, concrete with
      | [loan_root, loan], [concrete_root, extra_concrete_loan_root, concrete]
        when borrow_root != concrete_root ->
          Some {owner;marker;borrow_root;borrow_value;borrow;loan_root;loan;
            concrete_root;extra_concrete_loan_root;concrete}
      | _ -> None)
  | _ -> None

let component_roots (c : component) =
  [c.borrow_root;c.loan_root;c.concrete_root] @ Option.to_list c.extra_concrete_loan_root

(** Only typed ancestors of an explicitly selected leaf are rebuilt. Metadata
    fields and every unselected sibling are taken from the original object. *)
let rec replace replacements (v : tavalue) : tavalue =
  match List.find_opt (fun (original,_) -> original == v) replacements with
  | Some (_,changed) -> changed
  | None ->
      (match v.value with
      | AAdt adt ->
          let fields = List.map (replace replacements) adt.fields in
          if List.for_all2 (==) fields adt.fields then v
          else {v with value=AAdt {adt with fields}}
      | ALoan (AEndedIgnoredMutLoan ended) ->
          let child=replace replacements ended.child in
          let given_back=replace replacements ended.given_back in
          if child==ended.child && given_back==ended.given_back then v
          else {v with value=ALoan (AEndedIgnoredMutLoan {ended with child;given_back})}
      | _ -> v)

(** Metadata does not constitute a live A permission. Current E captures do:
    follow exactly the captured value through its own saved environment, never
    reinterpret the complete historical environment as today's ownership. *)
let check_captured_ids span sid bid snapshot value =
  let rec walk ancestors seen (value : tvalue) =
    require span (not (List.exists ((==) value) ancestors)) "cyclic captured value";
    let ancestors=value::ancestors in
    let different id = require span (id<>bid) "selected shared loan occurs in E/captured metadata" in
    match value.value with
    | VSymbolic symbolic ->
        require span (symbolic.sv_id<>sid) "selected symbolic value occurs in captured metadata"
    | VLiteral _ | VBottom -> ()
    | VAdt adt -> List.iter (walk ancestors seen) adt.fields
    | VLoan (VMutLoan id) -> different id
    | VLoan (VSharedLoan (id,value)) | VBorrow (VMutBorrow (id,value)) ->
        different id; walk ancestors seen value
    | VBorrow (VSharedBorrow (id,_) | VReservedMutBorrow (id,_)) ->
        different id;
        require span (not (BorrowId.Set.mem id seen)) "cyclic captured shared borrow";
        let env = match snapshot with
          | Some env -> env
          | None -> [%craise] span "Closed shared component: captured borrow has no saved environment" in
        let value=InterpBorrowsCore.lookup_shared_value span env id in
        walk ancestors (BorrowId.Set.add id seen) value
  in walk [] BorrowId.Set.empty value

let check_closed span (ctx : eval_ctx) (c : component) =
  let owner=c.owner and sid=c.borrow.proj.sv_id and bid=c.concrete.loan_id in
  let owners=List.filter_map (function EAbs abs -> Some abs | _ -> None) ctx.env in
  require span (List.length (List.filter (fun (abs : abs) -> abs.abs_id=owner.abs_id) owners)=1)
    "selected owner is not unique";
  ignore (InterpSharedPacketSignature.check ~allow_marked:true span ctx owner);
  let pc=P.context_of_eval ctx in
  let borrow_type=P.view_type pc owner c.borrow.proj.proj_ty in
  let loan_type=P.view_type pc owner c.loan.proj.proj_ty in
  require span (not borrow_type.owned_mutable && not loan_type.owned_mutable
    && equal_ty borrow_type.normalized loan_type.normalized)
    "selected component is not the same complete shared projection";
  let marker_count=ref 0 in
  let marker_visitor=object
    inherit [_] iter_tavalue
    method! visit_proj_marker () pm =
      if pm<>PNone then begin
        require span (pm=c.marker) "another side marker occurs in selected owner";
        incr marker_count
      end
  end in
  List.iter (marker_visitor#visit_tavalue ()) (component_roots c);
  require span (!marker_count=(if c.marker=PNone then 0 else 4))
    "selected component roots have additional marked endpoints";
  let shared_lookup=InterpSharedPacketSignature.lookup_retained_shared_value span ctx in
  let occurrences,runtime,issues=C.inventory ~shared_lookup span ctx.env
    (SymbolicValueId.Set.singleton sid) in
  require span (issues=[]) ("incomplete current inventory: " ^ String.concat "; " issues);
  require span (runtime=[]) "selected symbolic value has a current concrete dependency";
  let selected=List.filter (fun (o : C.occurrence) -> o.sid=sid) occurrences in
  require span (List.length selected=2 && List.for_all (fun (o : C.occurrence) ->
    o.owner==owner && o.marker=c.marker && match o.origin with
      | C.Packet p -> (match p with
          | AProjLoans p -> p==c.loan && o.level=0
          | AProjBorrows p -> p==c.borrow && o.level=1
          | _ -> false)
      | _ -> false) selected) "symbolic component is not closed at its two native levels";
  (* A/E identifiers and runtime carriers are scanned without entering opaque
     historical mvalues; E captures are examined separately below. *)
  let borrows=ref 0 and loans=ref 0 in
  let ids=object
    inherit [_] iter_eval_ctx
    method! visit_borrow_id () id = if id=bid then incr borrows
    method! visit_loan_id () id = if id=bid then incr loans
  end in
  ids#visit_eval_ctx () ctx;
  require span (!borrows=1 && !loans=1) "shared loan/borrow component has external current IDs";
  ignore (InterpPacketMerge.check_child_e_boundary ~current_env:ctx.env span pc owners sid);
  List.iter (fun (owner : abs) ->
    let d=P.describe_owner pc owner in
    List.iter (fun (capture : P.capture) ->
      check_captured_ids span sid bid (Some capture.snapshot) capture.value) d.captures;
    List.iter (fun (metadata : P.concrete_metadata) ->
      let unused = List.exists (fun (node : P.node) ->
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
      (* Native top-root filtering never reads this ignored payload. *)
      if not (unused || unused_root) then
        check_captured_ids span sid bid None metadata.value) d.concrete_metadata) owners;
  ConstGenericVarId.Map.iter (fun _ value -> check_captured_ids span sid bid None value)
    ctx.const_generic_vars_map;
  require span (not (InterpUtils.value_has_loans_or_borrows (Some span) ctx c.concrete.shared_value.value))
    "selected shared referent contains current permissions";
  require span (InterpBorrowsCore.projections_intersect span ctx
    owner.regions.owned c.borrow.proj.proj_ty owner.regions.owned c.loan.proj.proj_ty)
    "selected symbolic projections do not intersect"

let same_context_except_env (left : eval_ctx) (right : eval_ctx) =
  left.crate==right.crate && left.type_ctx==right.type_ctx && left.fun_ctx==right.fun_ctx
  && left.region_groups==right.region_groups && left.type_vars==right.type_vars
  && left.const_generic_vars==right.const_generic_vars
  && left.const_generic_vars_map==right.const_generic_vars_map
  && left.ended_regions==right.ended_regions
  && left.fresh_symbolic_value_id==right.fresh_symbolic_value_id
  && left.fresh_dummy_var_id==right.fresh_dummy_var_id
  && left.fresh_fun_call_id==right.fresh_fun_call_id && left.fresh_borrow_id==right.fresh_borrow_id
  && left.fresh_shared_borrow_id==right.fresh_shared_borrow_id
  && left.fresh_abs_id==right.fresh_abs_id && left.fresh_region_id==right.fresh_region_id
  && left.fresh_abs_fvar_id==right.fresh_abs_fvar_id && left.fresh_loop_id==right.fresh_loop_id
  && left.fresh_meta_id==right.fresh_meta_id
  && left.fresh_symbolic_expr_id==right.fresh_symbolic_expr_id

(** Synthesis callers opt in only after selecting a closed component. The
    native result below must still preserve the entire original continuation,
    including opaque captures, through the exact [Preserve.same_env] check. *)
let apply ?(allow_unchanged_cont=false) config span (ctx : eval_ctx) (c : component) =
  check_closed span ctx c;
  let pair=c.concrete in
  let unmarked = [
    c.borrow_value,{c.borrow_value with value=ASymbolic(PNone,AProjBorrows c.borrow)};
    c.loan_root,{c.loan_root with value=ASymbolic(PNone,AProjLoans c.loan)};
    pair.loan_value,{pair.loan_value with value=ALoan(ASharedLoan(PNone,pair.loan_id,pair.shared_value,pair.loan_child))};
    pair.borrow_value,{pair.borrow_value with value=ABorrow(ASharedBorrow(PNone,pair.loan_id,pair.shared_id))}
  ] in
  let originals=component_roots c in
  let view_owner={c.owner with avalues=List.map (replace unmarked) originals} in
  let view={ctx with env=[EAbs view_owner]} in
  let native=InterpBorrows.return_analysis_sublevel_borrows ~allow_unchanged_cont
      config span c.owner.abs_id 1 view in
  let native=InterpBorrows.end_unblocked_proj_loans span c.owner.abs_id
    c.owner.regions.owned c.loan.proj native in
  let native=InterpBorrows.end_loan_no_synth config span ~snapshots:false pair.loan_id native in
  require span (same_context_except_env view native) "native operation changed non-environment context";
  let native_borrow,native_loan = match native.env with
    | [EAbs {avalues={value=ALoan(AEndedIgnoredMutLoan ended);_}::
        {value=ASymbolic(PNone,AEndedProjLoans loan);_}::_;_}] ->
        (match ended.given_back.value with
        | ASymbolic(PNone,AEndedProjBorrows borrow) -> borrow,loan
        | _ -> [%craise] span "Closed shared component: native borrow did not end")
    | _ -> [%craise] span "Closed shared component: native owner shape changed" in
  let returned=native_borrow.mvalues.given_back in
  require span (native_borrow.mvalues.consumed=c.borrow.proj.sv_id
    && returned.sv_id<>c.borrow.proj.sv_id
    && equal_ty returned.sv_ty c.borrow.proj.proj_ty
    && equal_ty native_borrow.proj_ty c.borrow.proj.proj_ty && native_borrow.loans=[])
    "native returned symbolic metadata differs from exact borrow semantics";
  require span (native_loan.proj=c.loan.proj.sv_id
    && equal_ty native_loan.proj_ty c.loan.proj.proj_ty && native_loan.borrows=[]
    && match native_loan.consumed with
      | [metadata,AEmpty] -> metadata.sv_id=returned.sv_id
          && equal_ty metadata.proj_ty c.loan.proj.proj_ty
      | _ -> false) "native loan history differs from exact give-back semantics";
  let ended = [
    c.borrow_value,{c.borrow_value with value=ASymbolic(PNone,AEndedProjBorrows native_borrow)};
    c.loan_root,{c.loan_root with value=ASymbolic(PNone,AEndedProjLoans native_loan)};
    pair.loan_value,{pair.loan_value with value=ALoan(AEndedSharedLoan(pair.shared_value,pair.loan_child))};
    pair.borrow_value,{pair.borrow_value with value=ABorrow AEndedSharedBorrow}
  ] in
  let expected={c.owner with avalues=List.map (replace ended) originals} in
  require span (Preserve.same_env [EAbs expected] native.env)
    "native result changed unselected fields or historical metadata";
  let owner={c.owner with avalues=List.map (replace ended) c.owner.avalues} in
  let committed={ctx with env=List.map (function
    | EAbs old when old==c.owner -> EAbs owner
    | entry -> entry) ctx.env} in
  ignore (InterpSharedPacketSignature.check ~allow_marked:true span committed owner);
  Printf.eprintf "CLOSED_SHARED_COMPONENT_RETIRED owner=%s sid=%s loan=%s\n%!"
    (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string c.loan.proj.sv_id)
    (BorrowId.to_string pair.loan_id);
  committed

let retire config span ~with_abs_conts ~recording ~fixed_aids (ctx : eval_ctx) : eval_ctx =
  if with_abs_conts || recording || config.mode<>SymbolicMode then ctx
  else
    let rec run ctx =
      let candidate=List.find_map (function
        | EAbs owner when owner.can_end && owner.cont=None
            && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs
            && not (AbsId.Set.mem owner.abs_id fixed_aids) -> choose owner
        | _ -> None) ctx.env in
      match candidate with None -> ctx | Some component -> run (apply config span ctx component)
    in run ctx

let permission_free_history = InterpSharedHistory.permission_free_history
let empty_native_interface = InterpSharedHistory.empty_native_interface

(** Check the complete current projection masks across the native global region
    substitution, including other owners and E-let binders. Historical values
    keep the native substitution's treatment; no E expression is reconstructed. *)
let check_quotient_masks span ~merged_regions (before : eval_ctx) (after : eval_ctx) =
  let pc=P.context_of_eval before and qc=P.context_of_eval after in
  let owners env=List.filter_map(function EAbs owner->Some owner|_->None) env in
  let left=owners before.env and right=owners after.env in
  require span (List.length left=List.length right) "region quotient changed owner count";
  let check old_owned new_owned old_ty new_ty =
    require span (equal_ty (Substitute.erase_regions old_ty) (Substitute.erase_regions new_ty))
      "region quotient changed an erased native type";
    require span (equal_ty
      (InterpBorrowsCore.normalize_proj_ty old_owned old_ty)
      (InterpBorrowsCore.normalize_proj_ty new_owned new_ty))
      "region quotient changed a current projection mask" in
  List.iter2 (fun (a : abs) (b : abs) ->
    require span (a.abs_id=b.abs_id && a.kind=b.kind && a.can_end=b.can_end
      && AbsId.Set.equal a.parents b.parents && AbsLevelSet.equal a.ended_subabs b.ended_subabs)
      "region quotient changed owner identity or lifetime state";
    let d=P.describe_owner pc a and e=P.describe_owner qc b in
    require span (List.length d.nodes=List.length e.nodes
      && List.length d.packets=List.length e.packets
      && List.length d.bindings=List.length e.bindings)
      "region quotient changed a permission or continuation shape";
    List.iter2 (fun (x:P.node) (y:P.node) ->
      require span (x.path=y.path && x.surface=y.surface && x.level=y.level)
        "region quotient moved a native node";
      match x.original,y.original with
      | P.AValue x,P.AValue y -> check a.regions.owned b.regions.owned x.ty y.ty
      | P.EValue x,P.EValue y -> check a.regions.owned b.regions.owned x.ty y.ty
      | P.SharedReborrow (AsbProjReborrows x),P.SharedReborrow (AsbProjReborrows y) ->
          check a.regions.owned b.regions.owned x.proj_ty y.proj_ty
      | _ -> ()) d.nodes e.nodes;
    List.iter2 (fun (x:P.packet) (y:P.packet) ->
      require span (x.sid=y.sid && x.marker=y.marker && x.polarity=y.polarity && x.phase=y.phase)
        "region quotient changed a symbolic permission";
      check a.regions.owned b.regions.owned x.typ.full y.typ.full) d.packets e.packets;
    List.iter2 (fun (x:P.binding_site) (y:P.binding_site) ->
      (* The pattern alone may not mention a region used by the E-let body.
         Uniform membership protects every projection in that nested scope. *)
      let overlap=RegionId.Set.inter x.owned merged_regions in
      require span (RegionId.Set.is_empty overlap || RegionId.Set.equal overlap merged_regions)
        "region quotient would merge distinct E-let scope permissions";
      check x.owned y.owned x.pattern.ty y.pattern.ty) d.bindings e.bindings) left right;
  let symbolics env =
    let values=ref [] in
    let visitor=object
      inherit [_] iter_env
      method! visit_symbolic_value () value=values:=value::!values
    end in
    visitor#visit_env () env; List.rev !values in
  let before_values=symbolics before.env and after_values=symbolics after.env in
  require span (List.length before_values=List.length after_values)
    "region quotient changed current symbolic values";
  List.iter2 (fun (a:symbolic_value) (b:symbolic_value) ->
    require span (a.sv_id=b.sv_id) "region quotient changed a symbolic ID";
    List.iter2 (fun (x:abs) (y:abs) ->
      check x.regions.owned y.regions.owned a.sv_ty b.sv_ty) left right)
    before_values after_values

(** The reference-collecting loop has a fixed concrete source borrow followed
    by one shared symbolic input, one borrow-free shared loan, and one shared
    symbolic output. Fresh lifetimes introduced by each iteration all belong
    to this one analysis abstraction and therefore end together. Normalize
    only that group with the native region substitution, keeping the source
    borrow's lifetime separate and every permission ID/root in place. *)
let normalize_shared_collector span (ctx : eval_ctx) (owner : abs) =
  match owner.avalues with
  | [{value=ABorrow(ASharedBorrow(PNone,_,_));
      ty=TRef(RVar(Free source_region),_,RShared)};
     {value=ASymbolic(PNone,AProjBorrows {proj=input;loans=[]});_};
     ({value=ALoan(ASharedLoan(PNone,_,shared,child));
       ty=TRef(RVar(Free concrete_region),referent,RShared)} as concrete);
     {value=ASymbolic(PNone,AProjLoans {proj=output;consumed=[];borrows=[]});_}]
    when owner.cont=None && owner.can_end && AbsId.Set.is_empty owner.parents
      && AbsLevelSet.is_empty owner.ended_subabs
      && ValuesUtils.is_aignored child.value
      && equal_ty shared.ty (Substitute.erase_regions referent)
      && not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
      && not(InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared)
      && equal_ty (Substitute.erase_regions input.proj_ty)
          (Substitute.erase_regions output.proj_ty) ->
      let input_regions=InterpMatchCtxs.validate_symbolic_hierarchy_type span
        ctx.crate ctx.type_ctx.type_infos input.proj_ty in
      let output_regions=InterpMatchCtxs.validate_symbolic_hierarchy_type span
        ctx.crate ctx.type_ctx.type_infos output.proj_ty in
      let group=RegionId.Set.union input_regions output_regions in
      let all_regions=RegionId.Set.add concrete_region (RegionId.Set.add source_region group) in
      let concrete_only =
        if concrete_region=source_region then true else
          let used=ref false in
          let visitor=object(self)
            inherit [_] iter_env
            method! visit_region_id () region =
              if region=concrete_region then used:=true
            method! visit_abs () other =
              if other.abs_id<>owner.abs_id then
                RegionId.Set.iter (self#visit_region_id ()) other.regions.owned;
              List.iter (fun (value:tavalue) ->
                if value!=concrete then self#visit_tavalue () value) other.avalues;
              Option.iter (self#visit_abs_cont ()) other.cont
          end in
          visitor#visit_env () ctx.env;
          not !used in
      let separate=not(RegionId.Set.mem source_region group)
        && (concrete_region=source_region || not(RegionId.Set.mem concrete_region group))
        && concrete_only
        && RegionId.Set.cardinal input_regions=1
        && RegionId.Set.cardinal output_regions=1
        && (RegionId.Set.cardinal group>1 || concrete_region<>source_region)
        && RegionId.Set.equal owner.regions.owned all_regions
        && RegionId.Set.is_empty(RegionId.Set.inter all_regions ctx.ended_regions)
        && List.for_all (function
          | EAbs other when other.abs_id<>owner.abs_id ->
              RegionId.Set.is_empty(RegionId.Set.inter all_regions other.regions.owned)
              && not(AbsId.Set.mem owner.abs_id other.parents)
          | _ -> true) ctx.env in
      if not separate then ctx else begin
        (* A borrow-free concrete loan's outer region is its owner's ghost
           lifetime, not a projected symbolic referent permission. The fresh
           name occurs nowhere else in the current A/E state. Use the source
           shared borrow's lifetime for that leaf, and separately normalize
           the immutable symbolic input/output group. *)
        let ghost=if concrete_region=source_region then ctx else
          InterpAbs.ctx_merge_regions ctx source_region (RegionId.Set.singleton concrete_region) in
        if concrete_region<>source_region then
          check_quotient_masks span ~merged_regions:(RegionId.Set.of_list [source_region;concrete_region]) ctx ghost;
        let representative=RegionId.Set.min_elt input_regions in
        let after=InterpAbs.ctx_merge_regions ghost representative
          (RegionId.Set.remove representative group) in
        require span (same_context_except_env ctx after)
          "shared collector quotient changed non-environment state";
        check_quotient_masks span ~merged_regions:group ghost after;
        Invariants.check_invariants span after;
        after
      end
  | _ -> ctx

(** Analysis normalization follows the native merge region quotient, rather
    than pretending different owned sets are alpha-equivalent. Only a flat
    shared borrow/loan interface survives. Pure classification proves that
    removed historical roots contribute no consumed value or given-back pattern
    at any original level; retained continuations are never dropped. *)
let normalize_analysis config span ~with_abs_conts ~recording ~fixed_aids
    (ctx : eval_ctx) : eval_ctx =
  if with_abs_conts || recording || config.mode<>SymbolicMode then ctx
  else
    let normalize ctx aid =
      let owner=ctx_lookup_abs ctx aid in
      if not owner.can_end || owner.cont<>None
        || not (AbsId.Set.is_empty owner.parents)
        || not (AbsLevelSet.is_empty owner.ended_subabs)
        || AbsId.Set.mem aid fixed_aids then ctx
      else
        let removed,kept=List.partition (permission_free_history span ctx) owner.avalues in
        let flat_interface = match kept with
          | [{value=ASymbolic(PNone,AProjBorrows borrow);_};
             {value=ASymbolic(PNone,AProjLoans loan);_}] ->
              borrow.loans=[] && loan.consumed=[] && loan.borrows=[]
              && List.for_all (fun (value:tavalue) ->
                not (TypesUtils.ty_has_mut_borrow_for_region_in_set
                  ctx.type_ctx.type_infos owner.regions.owned value.ty)) kept
          | _ -> false in
        let mixed_interface =
          let borrows=ref 0 and loans=ref 0 and concrete=ref 0
          and concrete_loans=ref 0 in
          let flat (value:tavalue)=match value.value with
            | ASymbolic(PNone,AProjBorrows {loans=[];_}) ->
                incr borrows;
                not(TypesUtils.ty_has_mut_borrow_for_region_in_set
                  ctx.type_ctx.type_infos owner.regions.owned value.ty)
            | ASymbolic(PNone,AProjLoans {consumed=[];borrows=[];_}) ->
                incr loans;
                not(TypesUtils.ty_has_mut_borrow_for_region_in_set
                  ctx.type_ctx.type_infos owner.regions.owned value.ty)
            | ABorrow(ASharedBorrow(PNone,_,_)) ->
                incr concrete;
                (match value.ty with TRef(_,referent,RShared) ->
                  not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
                | _ -> false)
            | ALoan(ASharedLoan(PNone,_,shared,child)) ->
                incr concrete; incr concrete_loans;
                ValuesUtils.is_aignored child.value
                && not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos shared.ty)
                && not(InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared)
            | _ -> false in
          (* The surviving output may already be a concrete shared loan.
             Unused lifetime elimination below observes that original leaf's
             type/payload as well as every other current A/E root; it never
             quotients the live regions or changes the matching relation. *)
          let all_flat=List.for_all flat kept in
          let concrete_input=match kept with
            | [{value=ABorrow(ASharedBorrow(PNone,_,_));_};
               {value=ASymbolic(PNone,AProjLoans {consumed=[];borrows=[];_});_}] -> true
            | _ -> false in
          all_flat &&
          ((!borrows=1 && !concrete>0
            && (!loans=1 || (!loans=0 && !concrete_loans>0)))
           || concrete_input) in
        if mixed_interface then begin
          ignore(InterpSharedPacketSignature.check span ctx owner);
          require span (List.for_all (empty_native_interface span ctx owner) removed)
            "mixed analysis historical root still has a native Pure interface";
          let trimmed={owner with avalues=kept} in
          let before=fst(ctx_subst_abs span ctx aid trimmed) in
          (* Eliminate only unused existential lifetime names. Do NOT quotient
             live lifetimes: the concrete and symbolic endpoints can have
             distinct lifetimes even when this owner eventually ends both.
             Observe the entire current environment, original ELet scopes, and
             every other owner's owned set before forgetting a name. Opaque
             historical snapshots remain their original immutable objects. *)
          let used=ref RegionId.Set.empty in
          let visitor=object(self)
            inherit [_] iter_env as super
            method! visit_region_id () region=used:=RegionId.Set.add region !used
            method! visit_abs () other=
              if other.abs_id<>aid then used:=RegionId.Set.union other.regions.owned !used;
              List.iter(self#visit_tavalue ()) other.avalues;
              Option.iter(self#visit_abs_cont ()) other.cont
            method! visit_ELet () regions pattern bound next=
              used:=RegionId.Set.union regions !used;
              super#visit_ELet () regions pattern bound next
          end in
          visitor#visit_env () before.env;
          let owned=RegionId.Set.inter owner.regions.owned !used in
          require span (not(RegionId.Set.is_empty owned))
            "mixed analysis normalization lost all current lifetime owners";
          let after=fst(ctx_subst_abs span before aid {trimmed with regions={owned}}) in
          require span (same_context_except_env before after)
            "unused lifetime elimination changed non-environment context";
          check_quotient_masks span ~merged_regions:RegionId.Set.empty before after;
          Invariants.check_invariants span after;
          if Sys.getenv_opt "AENEAS_TRACE_SHARED_HISTORY"=Some "1" then
            Printf.eprintf "UNUSED_SHARED_HISTORY_NORMALIZED owner=%s roots=%d regions=%d->%d\n%!"
              (AbsId.to_string aid) (List.length removed)
              (RegionId.Set.cardinal owner.regions.owned) (RegionId.Set.cardinal owned);
          normalize_shared_collector span after (ctx_lookup_abs after aid)
        end
        else if removed=[] || not flat_interface then ctx
        else begin
          ignore (InterpSharedPacketSignature.check span ctx owner);
          require span (List.for_all (empty_native_interface span ctx owner) removed)
            "permission-free historical root still has a native Pure interface";
          require span (not (RegionId.Set.is_empty owner.regions.owned)
            && RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
            "analysis normalization needs live owned regions";
          env_iter_abs (fun other -> if other.abs_id<>aid then
            require span (RegionId.Set.is_empty
              (RegionId.Set.inter owner.regions.owned other.regions.owned))
              "analysis normalization has overlapping region owners") ctx.env;
          let trimmed={owner with avalues=kept} in
          let before=fst (ctx_subst_abs span ctx aid trimmed) in
          let representative=RegionId.Set.min_elt owner.regions.owned in
          let merged=RegionId.Set.remove representative owner.regions.owned in
          let after=InterpAbs.ctx_merge_regions before representative merged in
          require span (same_context_except_env before after)
            "native region quotient changed non-environment context";
          check_quotient_masks span ~merged_regions:owner.regions.owned before after;
          Invariants.check_invariants span after;
          Printf.eprintf "CLOSED_SHARED_HISTORY_NORMALIZED owner=%s roots=%d regions=%d->1\n%!"
            (AbsId.to_string aid) (List.length removed) (RegionId.Set.cardinal owner.regions.owned);
          after
        end in
    let ids=List.filter_map (function EAbs owner->Some owner.abs_id|_->None) ctx.env in
    List.fold_left normalize ctx ids
