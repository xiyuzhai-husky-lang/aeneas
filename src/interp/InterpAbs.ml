open Types
open Values
open Contexts
open ValuesUtils
open TypesUtils
open InterpUtils
open InterpBorrowsCore
open InterpBorrows

(** The local logger *)
let log = Logging.abs_log

(* Decompose all the shared loans inside a value *)
let rec decompose_shared_value span pm (rid : RegionId.id) (v : tvalue) :
    tavalue list * tvalue =
  match v.value with
  | VLiteral _ -> ([], v)
  | VAdt { variant_id; fields } ->
      let avll, fields =
        List.split (List.map (decompose_shared_value span pm rid) fields)
      in
      let v = { v with value = VAdt { variant_id; fields } } in
      (List.flatten avll, v)
  | VBottom -> [%internal_error] span
  | VBorrow _ -> [%craise] span "Nested borrows are not supported yet"
  | VLoan lc -> (
      match lc with
      | VSharedLoan (bid, sv) ->
          let vl, sv = decompose_shared_value span pm rid sv in
          [%cassert] span (ty_no_regions sv.ty)
            "Nested borrows are not supported yet";

          (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
          let ty = mk_ref_ty (RVar (Free rid)) sv.ty RShared in
          let av : tavalue =
            let ignored = mk_aignored span v.ty None in
            let value = ALoan (ASharedLoan (pm, bid, sv, ignored)) in
            { value; ty }
          in

          (* *)
          (vl @ [ av ], sv)
      | VMutLoan _ -> [%internal_error] span)
  | VSymbolic _ ->
      [%cassert] span (ty_no_regions v.ty)
        "Nested borrows are not supported yet";
      ([], v)

let convert_value_to_abstractions (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) (ctx : eval_ctx) (v : tvalue) : abs list =
  [%ltrace tvalue_to_string ctx v];
  (* Convert the value to a list of avalues *)
  let absl = ref [] in
  let current_value = ref ("root",v) in
  let push_abs (r_id : RegionId.id) (avalues : tavalue list)
      (output : tevalue option) (input : tevalue option) : unit =
    if avalues = [] then ()
    else begin
      (* There should be output and input expressions *)
      let output = [%unwrap_with_span] span output "Unexpected error" in
      let input = [%unwrap_with_span] span input "Unexpected error" in
      (* Create the abs - note that we keep the order of the avalues as it is
         (unlike the environments) *)
      [%ldebug
        "avalues:\n"
        ^ String.concat "\n"
            (List.map
               (fun (v : tavalue) ->
                 tavalue_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
               avalues)];
      let abs =
        {
          abs_id = ctx.fresh_abs_id ();
          kind = abs_kind;
          can_end;
          parents = AbsId.Set.empty;
          regions = { owned = RegionId.Set.singleton r_id };
          ended_subabs = AbsLevelSet.empty;
          avalues;
          cont = Some { output = Some output; input = Some input };
        }
      in
      [%ldebug "abs:\n" ^ abs_to_string span ctx abs];
      Invariants.opt_type_check_abs span ctx abs;
      (* Add to the list of abstractions *)
      absl := abs :: !absl
    end
  in

  (* We only call this on values inside mutable borrows *)
  let rec to_inputs (rid : RegionId.id) (v : tvalue) : tavalue list * tevalue =
    current_value := ("mutable-borrow input",v);
    match v.value with
    | VLiteral _ -> ([], { value = EValue (ctx.env, v); ty = v.ty })
    | VAdt { variant_id; fields } ->
        [%cassert] span (ty_no_regions v.ty)
          "Nested borrows are not supported yet";
        let avll, fields = List.split (List.map (to_inputs rid) fields) in
        let value = EAdt { borrow_proj = false; variant_id; fields } in
        let value : tevalue = { value; ty = v.ty } in
        (List.flatten avll, value)
    | VBottom ->
        [%cassert] span (ty_no_regions v.ty)
          "Nested borrows are not supported yet";
        ([], mk_ebottom v.ty)
    | VBorrow _ -> [%craise] span "Nested borrows are not supported yet"
    | VLoan lc -> (
        match lc with
        | VSharedLoan _ ->
            [%cassert] span (ty_no_regions v.ty)
              "Nested borrows are not supported yet";
            let avl, _ = decompose_shared_value span PNone rid v in
            let ev : tevalue = { value = EValue (ctx.env, v); ty = v.ty } in
            (avl, ev)
        | VMutLoan bid ->
            (* Push the avalue *)
            [%cassert] span (ty_no_regions v.ty)
              "Nested borrows are not supported yet";
            let inner_ty = v.ty in
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span v.ty in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free rid)) v.ty RMut in
            let av : tavalue =
              let value = ALoan (AMutLoan (PNone, bid, ignored None)) in
              { value; ty }
            in
            (* Create the input expression *)
            let input : tevalue =
              let value =
                ELoan (EMutLoan (PNone, bid, mk_eignored None inner_ty))
              in
              { value; ty }
            in
            (* *)
            ([ av ], input))
    | VSymbolic _ ->
        (* Check that there are no borrows in the symbolic value (otherwise it
           can't be an input value and we're in a case of nested borrows) *)
        [%cassert] span (ty_no_regions v.ty)
          "Nested borrows are not supported yet";
        ([], { value = EValue (ctx.env, v); ty = v.ty })
  in

  (* Convert a value to abstractions *)
  let rec to_abs (v : tvalue) : unit =
    current_value := ("abstraction conversion",v);
    match v.value with
    | VLiteral _ | VBottom -> ()
    | VAdt { variant_id = _; fields } -> List.iter to_abs fields
    | VBorrow (VMutBorrow (borrow_id, { value=VLoan (VMutLoan loan_id); ty=runtime_ty }))
      when InterpSharedPacketSignature.enabled () && not (ty_no_regions runtime_ty) ->
        (* An exact identity reborrow has no payload to expand or copy:
             MB old (ML new)  ->  abs { MB old _; ML new _ }.
           Recover both full endpoint types, then project a complete fresh
           identity hierarchy, including ignored inner return subscriptions.
           An outer-only owner would lose the inner loans on native return. *)
        let _,ref_ty,kind=ty_as_ref v.ty in
        [%cassert] span (kind=RMut && borrow_id<>loan_id && equal_ty ref_ty runtime_ty)
          "Nested identity reborrow changed its runtime reference type";
        let borrowed_ty=match ctx_lookup_loan span ek_all borrow_id ctx with
          | _,Abstract (AMutLoan (PNone,_,child)) -> child.ty
          | _ -> [%craise] span "Nested identity reborrow needs its original abstract mutable loan" in
        let loaned_ty=match lookup_borrow span ek_all (UMut loan_id) ctx with
          | Abstract (AMutBorrow (PNone,_,child)) -> child.ty
          | _ -> [%craise] span "Nested identity reborrow needs its original abstract mutable borrower" in
        List.iter (fun target ->
          [%cassert] span (equal_ty (Substitute.erase_regions target) runtime_ty)
            "Nested identity reborrow counterpart has a different erased referent";
          let check=object inherit [_] iter_ty
            method! visit_region () = function
              | RVar (Free region) ->
                  [%cassert] span (not (RegionId.Set.mem region ctx.ended_regions))
                    "Nested identity reborrow contains an ended interior region"
              | _ -> [%craise] span "Nested identity reborrow lacks a full live referent type"
          end in check#visit_ty () target;
          let info=TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos target in
          [%cassert] span (not (info.contains_mut_borrow || info.contains_static))
            "Nested identity reborrow currently supports only shared interior references")
          [borrowed_ty;loaned_ty];
        (* The endpoint names are independent instantiations. Require identical
           region-occurrence/alias structure, then allocate a bridge-local copy;
           no original region is substituted or identified with another one. *)
        let alpha ty =
          let _,fresh=RegionId.fresh_stateful_generator () in
          snd (ty_refresh_regions (Some span) fresh ty) in
        [%cassert] span (equal_ty (alpha borrowed_ty) (alpha loaned_ty))
          "Nested identity reborrow endpoints have different region alias structure";
        let inner_regions,target=ty_refresh_regions (Some span) ctx.fresh_region_id borrowed_ty in
        let outer=ctx.fresh_region_id () in
        let reference=mk_ref_ty (RVar (Free outer)) target RMut in
        let regions=outer::inner_regions in
        let parameters=List.map (fun index ->
          {index;name=None;variance=VaUnknown;mutability=LtUnknown}) regions in
        let sg:LlbcAst.bound_fun_sig={
          item_binder_params={empty_generic_params with regions=parameters};
          item_binder_value={is_unsafe=false;abi=AbiRust;is_variadic=false;
            inputs=[reference];output=reference}} in
        let groups=RegionsHierarchy.compute_regions_hierarchy_for_sig (Some span) ctx.crate sg in
        let ids=RegionGroupId.Map.of_list (List.map (fun (group:region_var_group) ->
          group.id,ctx.fresh_abs_id ()) groups) in
        [%cassert] span (RegionId.Set.equal (RegionId.Set.of_list regions)
          (RegionId.Set.of_list (List.concat_map (fun (group:region_var_group)->group.regions) groups)))
          "Nested identity bridge hierarchy lost a region";
        List.iter (fun (group:region_var_group) ->
          let owned=RegionId.Set.of_list group.regions in
          let owns_outer=RegionId.Set.mem outer owned in
          if owns_outer then
            [%cassert] span (group.regions=[outer])
              "Nested identity bridge outer and interior regions share a hierarchy group";
          let achild=mk_aignored span target None and echild=mk_eignored None target in
          let borrow:tavalue={ty=reference;value=ABorrow
            (if owns_outer then AMutBorrow(PNone,borrow_id,achild)
             else AIgnoredMutBorrow(Some borrow_id,achild))}
          and loan:tavalue={ty=reference;value=ALoan
            (if owns_outer then AMutLoan(PNone,loan_id,achild)
             else AIgnoredMutLoan(Some loan_id,achild))} in
          let output:tevalue={ty=reference;value=EBorrow
            (if owns_outer then EMutBorrow(PNone,borrow_id,echild)
             else EIgnoredMutBorrow(Some borrow_id,echild))}
          and input:tevalue={ty=reference;value=ELoan
            (if owns_outer then EMutLoan(PNone,loan_id,echild)
             else EIgnoredMutLoan(Some loan_id,echild))} in
          let abs={abs_id=RegionGroupId.Map.find group.id ids;kind=abs_kind;can_end;
            parents=AbsId.Set.of_list (List.map (fun id->RegionGroupId.Map.find id ids) group.parents);
            regions={owned};ended_subabs=AbsLevelSet.empty;avalues=[borrow;loan];
            cont=Some{output=Some output;input=Some input}} in
          Invariants.opt_type_check_abs span ctx abs;
          absl:=abs::!absl) groups
    | VBorrow bc -> (
        let _, ref_ty, kind = ty_as_ref v.ty in
        [%cassert] span (ty_no_regions ref_ty)
          "Nested borrows are not supported yet";
        match bc with
        | VSharedBorrow (bid, sid) ->
            (* Push a region abstraction for this borrow *)
            let rid = ctx.fresh_region_id () in
            let ty = TRef (RVar (Free rid), ref_ty, kind) in
            let value = ABorrow (ASharedBorrow (PNone, bid, sid)) in
            let value : tavalue = { value; ty } in
            let ev_out = Some (mk_etuple ~borrow_proj:true []) in
            let ev_in = Some (mk_etuple ~borrow_proj:false []) in
            push_abs rid [ value ] ev_out ev_in
        | VMutBorrow (bid, bv) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not (value_has_borrows (Some span) ctx bv.value))
              "Nested borrows are not supported yet";
            (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
            let rid = ctx.fresh_region_id () in
            let ty = TRef (RVar (Free rid), ref_ty, kind) in
            let av : tavalue =
              let ignored = mk_aignored span ref_ty None in
              let av = ABorrow (AMutBorrow (PNone, bid, ignored)) in
              { value = av; ty }
            in
            (* Create the output expression *)
            let output : tevalue =
              let ignored = mk_eignored None ref_ty in
              let value = EBorrow (EMutBorrow (PNone, bid, ignored)) in
              { value; ty }
            in
            (* Recursively explore the expression to look for shared loans
               and create the input expression *)
            let avl, input = to_inputs rid bv in
            push_abs rid (av :: avl) (Some output) (Some input)
        | VReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            [%craise] span "Unexpected")
    | VLoan _ ->
        let rid = ctx.fresh_region_id () in
        let avl, input = to_inputs rid v in
        (* Create a let-binding to ignore the input *)
        let rids = RegionId.Set.singleton rid in
        let input : tevalue =
          let value =
            ELet
              ( rids,
                mk_epat_ignored input.ty,
                input,
                mk_etuple ~borrow_proj:true [] )
          in
          { value; ty = mk_unit_ty }
        in
        (* *)
        let output = mk_eignored None mk_unit_ty in
        push_abs rid avl (Some output) (Some input)
    | VSymbolic sv ->
        (* Check that there are no nested borrows in the symbolic value -
           we don't support this case yet *)
        [%cassert] span
          (not
             (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
          "Nested borrows are not supported yet";

        (* Introduce one abstraction per live region *)
        let regions, ty = refresh_live_regions_in_ty span ctx sv.sv_ty in
        RegionId.Map.iter
          (fun _ rid ->
            let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty = ty } in
            let nv = ASymbolic (PNone, AProjBorrows { proj; loans = [] }) in
            let nv : tavalue = { value = nv; ty } in
            (* Abstraction expression *)
            let output =
              ESymbolic
                ( PNone,
                  EProjBorrows
                    { proj = { sv_id = sv.sv_id; proj_ty = ty }; loans = [] } )
            in
            let output = { value = output; ty } in
            let input = { value = EValue (ctx.env, v); ty } in
            let output,input =
              let info=TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos ty in
              if InterpSharedPacketSignature.enabled () && info.contains_borrow
                && not info.contains_mut_borrow && not info.contains_nested_borrows
                && not info.contains_static then
                (* Pure shared projections keep their whole A permission, but
                   have no backward value. This is the same empty continuation
                   used above for concrete shared borrows and by native
                   abstraction synthesis, which emits E projectors only for
                   mutable projected regions. Do not manufacture a mutable
                   output from a moved Vec<&T> (or another shared-only value). *)
                mk_etuple ~borrow_proj:true [], mk_etuple ~borrow_proj:false []
              else output,input in
            push_abs rid [ nv ] (Some output) (Some input))
          regions
  in

  (* Preserve the original failure while exposing the exact runtime node. *)
  try
    to_abs v;
    List.rev !absl
  with error ->
    let backtrace=Printexc.get_raw_backtrace () in
    let phase,current = !current_value in
    Printf.eprintf "VALUE_TO_ABSTRACTIONS_REJECTED phase=%s\ncurrent: %s\noriginal: %s\n%!"
      phase (show_tvalue current) (show_tvalue v);
    Printexc.raise_with_backtrace error backtrace

(** Before reducing an exact identity reborrow, deliver the native returns
    instead of deleting a mutable edge with external return subscriptions.
    This runs only in analysis: the caller keeps ordinary synthesis/recording
    on its existing path. All current permissions are changed by end_abs. *)
let end_subscribed_identity_reborrows (config : config) (span : Meta.span)
    (fixed_aids : AbsId.Set.t) (before_conversion : eval_ctx) (ctx0 : eval_ctx) : eval_ctx =
  if not (InterpSharedPacketSignature.enabled ()) || config.mode<>SymbolicMode then ctx0
  else
    let identity (owner:abs) =
      if Option.is_some (ctx_lookup_abs_opt before_conversion owner.abs_id)
        || not owner.can_end || AbsId.Set.mem owner.abs_id fixed_aids
        || not (AbsId.Set.is_empty owner.parents)
        || not (AbsLevelSet.is_empty owner.ended_subabs) then None
      else match owner.avalues,owner.cont with
      | [{value=ABorrow(AMutBorrow(PNone,old_id,{value=AIgnored None;ty=old_ty}));ty=old_ref};
         {value=ALoan(AMutLoan(PNone,new_id,{value=AIgnored None;ty=new_ty}));ty=new_ref}],
        Some {output=Some {value=EBorrow(EMutBorrow(PNone,out_id,{value=EIgnored None;ty=out_ty}));ty=out_ref};
              input=Some {value=ELoan(EMutLoan(PNone,in_id,{value=EIgnored None;ty=in_ty}));ty=in_ref}}
        when old_id<>new_id && old_id=out_id && new_id=in_id
          && equal_ty old_ty out_ty && equal_ty new_ty in_ty
          && equal_ty old_ref out_ref && equal_ty new_ref in_ref
          && equal_ty (Substitute.erase_regions old_ty) (Substitute.erase_regions new_ty)
          && not (ty_no_regions old_ty) ->
          (match old_ref,new_ref with
          | TRef(RVar(Free r),t,RMut),TRef(RVar(Free s),u,RMut)
            when r=s && RegionId.Set.equal owner.regions.owned (RegionId.Set.singleton r)
              && equal_ty t old_ty && equal_ty u new_ty
              && not (RegionId.Set.mem r (ty_regions old_ty))
              && not (RegionId.Set.mem r (ty_regions new_ty)) -> Some (old_id,new_id)
          | _ -> None)
      | _ -> None in
    let subscribers ctx bid =
      let found=ref false in
      let visitor=object inherit [_] iter_tavalue as super
        method! visit_AIgnoredMutLoan () id child =
          if id=Some bid then found:=true;
          super#visit_AIgnoredMutLoan () id child
      end in
      env_iter_abs (fun owner->List.iter (visitor#visit_tavalue ()) owner.avalues) ctx.env;
      !found in
    let named_borrows (value:tvalue) =
      let found=ref UniqueBorrowIdSet.empty in
      let visitor=object inherit [_] iter_tvalue as super
        method! visit_borrow_content () borrow =
          let id=match borrow with
            | VMutBorrow(bid,_)->UMut bid
            | VSharedBorrow(bid,sid)|VReservedMutBorrow(bid,sid)->UShared(bid,sid) in
          found:=UniqueBorrowIdSet.add id !found;
          super#visit_borrow_content () borrow
      end in visitor#visit_tvalue () value;!found in
    let candidates=List.filter_map (function
      | EAbs owner -> (match identity owner with Some _->Some owner.abs_id|None->None)
      | _->None) ctx0.env in
    List.fold_left (fun ctx aid -> match ctx_lookup_abs_opt ctx aid with
      | None->ctx
      | Some owner -> (match identity owner with
        | Some(old_id,new_id) when subscribers ctx old_id ->
            let result,_ = end_abs config span ~snapshots:false aid 0 ctx in
            AbsId.Set.iter (fun id ->
              [%classert] span (ctx_lookup_abs_opt ctx id = ctx_lookup_abs_opt result id)
                (lazy ("Native identity return changed fixed owner " ^ AbsId.to_string id))) fixed_aids;
            List.iter (function
              | EBinding(BVar binder,value) ->
                  let after=List.find_map (function
                    | EBinding(BVar other,value) when other.index=binder.index->Some value
                    | _->None) result.env in
                  [%classert] span (match after with
                    | Some after -> UniqueBorrowIdSet.subset (named_borrows value) (named_borrows after)
                    | None->false)
                    (lazy ("Native identity return would discard named borrow permissions in local "
                      ^ Expressions.LocalId.to_string binder.index
                      ^ "\nbefore: " ^ show_tvalue value
                      ^ "\nafter: " ^ (match after with Some v->show_tvalue v|None->"absent")))
              | _->()) ctx.env;
            [%cassert] span (ctx_lookup_abs_opt result aid=None && not (subscribers result old_id))
              "Native identity return left its owner or old-loan subscriptions active";
            Invariants.check_invariants span result;
            Printf.eprintf "IDENTITY_REBORROW_NATIVE_RETURN owner=%s old=%s new=%s\n%!"
              (AbsId.to_string aid) (BorrowId.to_string old_id) (BorrowId.to_string new_id);
            result
        | _->ctx)) ctx0 candidates

(** Move a regular shared alias out of a fully shared ended-loan cell. This is
    deliberately a context operation: the alias must not occur both in its old
    cell and in the separate permission-only abstraction. *)
let normalize_ended_shared_aliases ?(strict_shared_roots = false) (span : Meta.span)
    (fixed_aids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  if Sys.getenv_opt "AENEAS_EXPERIMENTAL_ENDED_SHARED_MOVE" <> Some "1" then ctx
  else
    let count_live_alias ctx lid sid =
      let count = ref 0 in
      let bump bid shared_id =
        if bid = lid && shared_id = sid then incr count
      in
      let visitor = object
        inherit [_] iter_eval_ctx
        (* Captured expression environments/metadata are not regular permissions. *)
        method! visit_abs_cont _ _ = ()
        method! visit_VSharedBorrow _ bid shared_id = bump bid shared_id
        method! visit_ASharedBorrow _ _ bid shared_id = bump bid shared_id
        method! visit_AsbBorrow _ bid shared_id = bump bid shared_id
      end in
      visitor#visit_eval_ctx () ctx;
      !count
    in
    let moved = ref [] in
    let normalize_abs (abs : abs) : env_elem list =
      let has_cont = match abs.cont with
        | Some { input = Some _; output = Some _ } -> true
        | _ -> false
      in
      if AbsId.Set.mem abs.abs_id fixed_aids || not abs.can_end || not has_cont
      then [EAbs abs]
      else
        let extra = ref [] in
        let rec visit (av : tavalue) : tavalue =
          match av.value with
          | AAdt adt ->
              { av with value = AAdt { adt with fields = List.map visit adt.fields } }
          | ALoan (AEndedSharedLoan (sv, child)) ->
              let eligible =
                match (av.ty, child.ty, sv.value, child.value) with
                | (TRef (RVar (Free outer), expected_child, RShared),
                   TRef (RVar (Free inner), referent, RShared),
                   VBorrow (VSharedBorrow (lid, sid)), AIgnored metadata) ->
                    let metadata_matches = match metadata with
                      | None -> true
                      | Some { value = VSymbolic original; ty = metadata_ty } ->
                          Types.equal_ty original.sv_ty child.ty
                          && Types.equal_ty metadata_ty (Substitute.erase_regions child.ty)
                      | _ -> false
                    in
                    let owner_matches =
                      match ctx_lookup_loan_opt span ek_all lid ctx with
                      | Some (AbsId owner_id, Abstract (ASharedLoan (PNone, _, value, leaf))) ->
                          let owner = ctx_lookup_abs ctx owner_id in
                          owner_id <> abs.abs_id
                          && RegionId.Set.mem inner owner.regions.owned
                          && AbsId.Set.mem abs.abs_id owner.parents
                          && Types.equal_ty value.ty (Substitute.erase_regions referent)
                          && not (tvalue_has_loans_or_borrows (Some span) ctx value)
                          && (match leaf.value with
                              | AIgnored None -> true
                              | AIgnored (Some meta) -> Values.equal_tvalue meta value
                              | _ -> false)
                      | _ -> false
                    in
                    if RegionId.Set.mem outer abs.regions.owned
                       && not (RegionId.Set.mem inner abs.regions.owned)
                       && Types.equal_ty expected_child child.ty
                       && Types.equal_ty sv.ty (Substitute.erase_regions child.ty)
                       && ty_no_regions referent
                       && not (ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
                       && metadata_matches && owner_matches
                       && count_live_alias ctx lid sid = 1
                       && not (List.mem (lid, sid) !moved)
                    then Some (lid, sid) else None
                | _ -> None
              in
              (match eligible with
               | None -> av
               | Some (lid, sid) ->
                   (* The established conversion retains lid/sid, introduces its
                      own fresh owned region and a unit input/output continuation. *)
                   let absl = convert_value_to_abstractions span Identity
                     ~can_end:true ctx sv in
                   (match absl with
                    | [{ avalues = [{ value = ABorrow (ASharedBorrow (PNone, lid', sid')); _ }]; _ }] ->
                        [%sanity_check] span (lid = lid' && sid = sid')
                    | _ -> [%craise] span "Unexpected shared-alias conversion");
                   moved := (lid, sid) :: !moved;
                   extra := List.rev_append absl !extra;
                   if Sys.getenv_opt "AENEAS_TRACE_ENDED_SHARED_MOVE" = Some "1" then
                     Printf.eprintf "ENDED_SHARED_MOVE abs=%s loan=%s sid=%s\n%!"
                       (AbsId.to_string abs.abs_id) (BorrowId.to_string lid)
                       (SharedBorrowId.to_string sid);
                   (* Only this regular permission cell moves. The old explicit
                      continuation and every captured expression value remain. *)
                   mk_aignored span av.ty None)
          | _ -> av
        in
        let avalues = List.map (fun (av : tavalue) ->
          (* A mixed mutable ADT may consume unfiltered shared fields. Do not
             traverse it. All selected top roots project only Shared/Unknown. *)
          let reject_root =
            ty_has_mut_borrows ctx.type_ctx.type_infos av.ty
            || (strict_shared_roots &&
                let info = TypesAnalysis.analyze_ty (Some span)
                  ctx.type_ctx.type_infos av.ty in
                info.contains_mut_borrow || info.contains_static)
          in
          if reject_root then av else visit av)
          abs.avalues in
        EAbs { abs with avalues } :: List.map (fun a -> EAbs a) (List.rev !extra)
    in
    let env = List.concat_map (function
      | EAbs abs -> normalize_abs abs
      | ee -> [ee]) ctx.env in
    let result = { ctx with env } in
    List.iter (fun (lid, sid) ->
      [%sanity_check] span (count_live_alias result lid sid = 1)) !moved;
    Invariants.check_invariants span result;
    result

(** At the single-context multi-exit loop boundary, use the same permission
    move with the stronger whole-selected-root native borrow analysis. Other
    call sites retain their existing domain and the continuation is untouched. *)
let normalize_after_loop_ended_shared_aliases (span : Meta.span)
    (fixed_aids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  if Sys.getenv_opt "AENEAS_EXPERIMENTAL_AFTER_LOOP_SHARED_MOVE" <> Some "1"
  then ctx
  else normalize_ended_shared_aliases ~strict_shared_roots:true span fixed_aids ctx

let convert_value_to_output_avalues (span : Meta.span) (ctx : eval_ctx)
    (pm : proj_marker) (v : tvalue) (regions : RegionId.Set.t) (proj_ty : ty) :
    tavalue list * tevalue =
  [%ltrace tvalue_to_string ctx v];

  let keep_region (r : region) =
    match r with
    | RVar (Free rid) -> RegionId.Set.mem rid regions
    | _ -> false
  in

  (* We only call this on values inside mutable borrows *)
  let rec check_inputs (v : tvalue) (proj_ty : ty) : unit =
    match (v.value, proj_ty) with
    | VLiteral _, _ -> ()
    | VAdt { variant_id; fields }, TAdt tref ->
        [%cassert] span (ty_no_regions v.ty)
          "Nested borrows are not supported yet";
        let field_types =
          ctx_adt_get_instantiated_field_types span ctx tref variant_id
        in
        List.iter2 check_inputs fields field_types
    | VBottom, _ -> [%internal_error] span
    | VBorrow _, _ -> [%craise] span "Nested borrows are not supported yet"
    | VLoan _, _ -> [%internal_error] span
    | VSymbolic _, _ ->
        if ty_no_regions v.ty then () else [%craise] span "Not implemented yet"
    | _ -> [%internal_error] span
  in

  (* Convert a value to abstractions *)
  let rec to_output (v : tvalue) (proj_ty : ty) : tavalue list * tevalue =
    match (v.value, proj_ty) with
    | VLiteral _, _ -> ([], mk_eignored (Some (ctx.env, v)) proj_ty)
    | VBottom, _ -> [%internal_error] span
    | VAdt { variant_id; fields }, TAdt tref ->
        let field_types =
          ctx_adt_get_instantiated_field_types span ctx tref variant_id
        in
        let avalues, outputs =
          List.split (List.map2 to_output fields field_types)
        in
        ( List.flatten avalues,
          {
            value = EAdt { borrow_proj = true; variant_id; fields = outputs };
            ty = proj_ty;
          } )
    | VBorrow bc, TRef (rid, ref_ty, kind) ->
        [%cassert] span (ty_no_regions ref_ty)
          "Nested borrows are not supported yet";
        if keep_region rid then
          match bc with
          | VSharedBorrow (bid, sid) ->
              (* Push a region abstraction for this borrow *)
              let rid = ctx.fresh_region_id () in
              let ty = TRef (RVar (Free rid), ref_ty, kind) in
              let value = ABorrow (ASharedBorrow (pm, bid, sid)) in
              let value : tavalue = { value; ty } in
              let ev = mk_etuple ~borrow_proj:true [] in
              ([ value ], ev)
          | VMutBorrow (bid, bv) ->
              (* We don't support nested borrows for now *)
              [%cassert] span
                (not (value_has_borrows (Some span) ctx bv.value))
                "Nested borrows are not supported yet";
              (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
              let av : tavalue =
                let ignored = mk_aignored span ref_ty None in
                let av = ABorrow (AMutBorrow (pm, bid, ignored)) in
                { value = av; ty = proj_ty }
              in
              (* Create the output expression *)
              let output : tevalue =
                let ignored = mk_eignored (Some (ctx.env, v)) ref_ty in
                let value = EBorrow (EMutBorrow (pm, bid, ignored)) in
                { value; ty = proj_ty }
              in
              (* Check the borrowed value *)
              check_inputs bv ref_ty;
              ([ av ], output)
          | VReservedMutBorrow _ ->
              (* This borrow should have been activated *)
              [%craise] span "Unexpected"
        else ([], mk_eignored (Some (ctx.env, v)) proj_ty)
    | VLoan _, _ ->
        (* TODO: should we project it or not (in which region abstraction should we put it)?
           We probably need to look at the borrows *inside*. *)
        [%craise] span "Not implemented yet"
    | VSymbolic sv, _ ->
        (* Check that there are no nested borrows in the symbolic value -
           we don't support this case yet *)
        [%cassert] span
          (not
             (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
          "Nested borrows are not supported yet";

        (* Check if there is an intersection with the current regions *)
        if ty_has_regions_in_set regions proj_ty then
          let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty } in
          let nv = ASymbolic (pm, AProjBorrows { proj; loans = [] }) in
          let nv : tavalue = { value = nv; ty = proj_ty } in
          (* Abstraction expression *)
          let output =
            ESymbolic
              ( pm,
                EProjBorrows
                  { proj = { sv_id = sv.sv_id; proj_ty }; loans = [] } )
          in
          let output = { value = output; ty = proj_ty } in
          (* *)
          ([ nv ], output)
        else ([], mk_eignored (Some (ctx.env, v)) proj_ty)
    | _ -> [%internal_error] span
  in

  (* Apply *)
  to_output v proj_ty

let convert_value_to_input_avalues (span : Meta.span) (ctx : eval_ctx)
    (pm : proj_marker) (v : tvalue) (rid : RegionId.id) : tavalue list * tevalue
    =
  [%ltrace tvalue_to_string ctx v];

  (* Convert a value to abstractions *)
  let rec to_input (v : tvalue) : tavalue list * tevalue =
    match v.value with
    | VLiteral _ -> ([], mk_evalue ctx.env v.ty v)
    | VBottom -> [%internal_error] span
    | VAdt { variant_id; fields } ->
        let avalues, outputs = List.split (List.map to_input fields) in
        ( List.flatten avalues,
          {
            value = EAdt { borrow_proj = false; variant_id; fields = outputs };
            ty = v.ty;
          } )
    | VBorrow _ -> [%craise] span "Not implemented yet"
    | VLoan lc -> (
        match lc with
        | VSharedLoan _ ->
            let avl, sv = decompose_shared_value span pm rid v in
            (avl, mk_evalue ctx.env sv.ty sv)
        | VMutLoan bid ->
            [%cassert] span (ty_no_regions v.ty)
              "Nested borrows are not supported yet";
            let inner_ty = v.ty in
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span v.ty in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free rid)) v.ty RMut in
            let av : tavalue =
              let value = ALoan (AMutLoan (pm, bid, ignored None)) in
              { value; ty }
            in
            (* Create the input expression *)
            let input : tevalue =
              let value =
                ELoan
                  (EMutLoan (pm, bid, mk_eignored (Some (ctx.env, v)) inner_ty))
              in
              { value; ty }
            in
            (* *)
            ([ av ], input))
    | VSymbolic sv ->
        (* Check that there are no nested borrows in the symbolic value -
           we don't support this case yet *)
        [%cassert] span
          (not
             (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
          "Nested borrows are not supported yet";
        [%cassert] span (not (tvalue_has_bottom ctx v)) "Unexpected";

        if ty_no_regions sv.sv_ty then ([], mk_evalue ctx.env v.ty v)
        else
          (* We project all the remaining regions: substitute all the regions
           with the region we're using for the abstraction. *)
          let _, proj_ty =
            ty_refresh_regions (Some span) (fun _ -> rid) sv.sv_ty
          in

          let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty } in
          let nv =
            ASymbolic (pm, AProjLoans { proj; consumed = []; borrows = [] })
          in
          let nv : tavalue = { value = nv; ty = proj_ty } in
          (* Abstraction expression *)
          let output =
            ESymbolic
              ( pm,
                EProjLoans
                  {
                    proj = { sv_id = sv.sv_id; proj_ty };
                    consumed = [];
                    borrows = [];
                  } )
          in
          let output = { value = output; ty = proj_ty } in
          (* *)
          ([ nv ], output)
  in

  (* Apply *)
  to_input v

(** Simplify the duplicated shared borrows in a region abstraction.

    {[
      abs { SB l0, SB l0 } ~> abs { SB l0 }
    ]}

    Note that this function supports projection markers: when merging two
    borrows we take the union of the markers. *)
let abs_simplify_duplicated_borrows (_span : Meta.span) (_ctx : eval_ctx)
    (abs : abs) : abs =
  let join_pm (pm0 : proj_marker) (pm1 : proj_marker) : proj_marker =
    match (pm0, pm1) with
    | PNone, _ | _, PNone -> PNone
    | PLeft, PRight | PRight, PLeft -> PNone
    | PRight, PRight -> PRight
    | PLeft, PLeft -> PLeft
  in

  (* We first filter the borrows which are duplicated *)
  let shared_borrows = ref BorrowId.Map.empty in
  let keep_avalue (av : tavalue) : bool =
    match av.value with
    | ABorrow (ASharedBorrow (pm, bid, _)) -> begin
        match BorrowId.Map.find_opt bid !shared_borrows with
        | None ->
            shared_borrows := BorrowId.Map.add bid pm !shared_borrows;
            true
        | Some pm' ->
            let pm = join_pm pm pm' in
            shared_borrows := BorrowId.Map.add bid pm !shared_borrows;
            false
      end
    | _ -> true
  in
  let avalues = List.filter keep_avalue abs.avalues in

  (* We update the projection markers of the remaining borrows *)
  let update_avalue (av : tavalue) : tavalue =
    match av.value with
    | ABorrow (ASharedBorrow (_, bid, sid)) ->
        let pm = BorrowId.Map.find bid !shared_borrows in
        { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
    | _ -> av
  in
  let avalues = List.map update_avalue avalues in

  (* Update the abstraction *)
  { abs with avalues }

type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    tavalue ->
    rty ->
    proj_marker ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [sid0]
          - [ty1]
          - [pm1]
          - [sid1] *)
  merge_amut_loans :
    loan_id ->
    rty ->
    proj_marker ->
    tavalue ->
    rty ->
    proj_marker ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored]. *)
  merge_ashared_loans :
    loan_id ->
    rty ->
    proj_marker ->
    tvalue ->
    tavalue ->
    rty ->
    proj_marker ->
    tvalue ->
    tavalue ->
    tavalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [pm0]
          - [sv0]
          - [child0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [child1] *)
  merge_aborrow_projs :
    ty ->
    proj_marker ->
    aproj_borrows ->
    ty ->
    proj_marker ->
    aproj_borrows ->
    tavalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [loans0]
          - [ty1]
          - [pm1]
          - [proj1]
          - [loans1] *)
  merge_aloan_projs :
    ty ->
    proj_marker ->
    aproj_loans ->
    ty ->
    proj_marker ->
    aproj_loans ->
    tavalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [consumed0]
          - [borrows0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [proj_ty1]
          - [children1] *)
}

(** Small utility: if a value doesn't have any marker, split it into two values
    with complementary markers. We use this for {!merge_abstractions}.

    We assume the value has been destructured (there are no nested loans, adts,
    the children are ignored, etc.). *)
let tavalue_split_marker (span : Meta.span) (ctx : eval_ctx) (owner : abs)
    (av : tavalue) :
    tavalue list =
  let mk_split mk_value = [ mk_value PLeft; mk_value PRight ] in
  let mk_opt_split pm mk_value =
    if pm = PNone then mk_split mk_value else [ av ]
  in
  match av.value with
  | AAdt _ -> [%craise] span "Not implemented yet"
  | AIgnored _ ->
      (* Nothing to do *)
      [ av ]
  | ABorrow bc -> (
      match bc with
      | AMutBorrow (pm, bid, child) ->
          [%sanity_check] span (is_aignored child.value);
          let mk_value pm =
            { av with value = ABorrow (AMutBorrow (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedBorrow (pm, bid, sid) ->
          let mk_value pm =
            { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
          in
          mk_opt_split pm mk_value
      | _ -> [%internal_error] span)
  | ALoan lc -> (
      match lc with
      | AMutLoan (pm, bid, child) ->
          [%sanity_check] span (is_aignored child.value);
          let mk_value pm =
            { av with value = ALoan (AMutLoan (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedLoan (pm, bids, sv, child) ->
          [%sanity_check] span (is_aignored child.value);
          (match sv.value with
           | VBorrow(VSharedBorrow _) when InterpSharedPacketSignature.enabled () ->
               (* The inner concrete borrow inherits each resulting branch
                  marker; its original unique ID is preserved on that branch. *)
               InterpSharedPacketSignature.check_retained_shared_loan
                 ~allow_marked:true span ctx owner 0 av
           | _ -> [%sanity_check] span
               (not (value_has_borrows (Some span) ctx sv.value)));
          let mk_value pm =
            { av with value = ALoan (ASharedLoan (pm, bids, sv, child)) }
          in
          mk_opt_split pm mk_value
      | _ ->
          [%craise] span
            ("Unsupported loan during marker splitting: "
             ^ tavalue_to_string ~with_ended:true ctx av ^ "\n"
             ^ abs_to_string span ~with_ended:true ctx owner))
  | ASymbolic (pm, proj) -> (
      if pm <> PNone then [ av ]
      else
        match proj with
        | AProjBorrows { proj = _; loans } ->
            [%sanity_check] span (loans = []);
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AProjLoans { proj = _; consumed; borrows } ->
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            [%internal_error] span)

let abs_split_markers (span : Meta.span) (ctx : eval_ctx) (abs : abs) : abs =
  {
    abs with
    avalues = List.concat (List.map (tavalue_split_marker span ctx abs) abs.avalues);
  }

(** Auxiliary function for {!merge_abstractions}.

    Phase 1 of the merge: we simplify all loan/borrow pairs, if a loan is in the
    left abstraction and its corresponding borrow is in the right abstraction.

    Important: this is asymmetric (the loan must be in the left abstraction).

    Example:
    {[
      abs0 { ML l0, MB l1 } |><| abs1 { MB l0 }
          ~~> abs1 { MB l1 }
    ]}

    But:
    {[
      abs1 { MB l0 } |><| abs0 { ML l0, MB l1 }
          ~~> abs1 { MB l0, ML l0, MB l1 }
    ]}

    We return the list of merged values.

    **Remark:** we assume the abstractions have been destructured and that the
    markers have been split (if markers are allowed). *)
let merge_abstractions_merge_loan_borrow_pairs (span : Meta.span)
    ~(allow_markers : bool) (ctx : eval_ctx) (abs0 : abs) (abs1 : abs) :
    tavalue list =
  [%ltrace ""];

  (* Sanity check: no markers appear unless we allow merging duplicates.
     Also, the borrows must be disjoint, and the loans must be disjoint. *)
  if not allow_markers then (
    let visitor =
      object
        inherit [_] iter_abs
        method! visit_proj_marker _ pm = [%sanity_check] span (pm = PNone)
      end
    in
    visitor#visit_abs () abs0;
    visitor#visit_abs () abs1);

  (* Merge.

     We take the values in the left abstraction and add the values from
     the right abstraction one at a time. Whenever we add a value, we go
     through all the *left* values in the abstraction to check if we need
     to eliminate a shared borrow because there is already a shared loan,
     or to check if we need to merge a mutable borrow and a mutable loan, etc.

     Note that we also filter the left avalues to remove ended loans, etc.
  *)
  let keep_avalue (v : tavalue) : bool =
    match v.value with
    | ALoan (AEndedSharedLoan (sv, child))
      when (not (value_has_loans_or_borrows (Some span) ctx sv.value))
           && is_aignored child.value -> false
    | AIgnored _ -> false
    | ASymbolic (_, AEndedProjLoans { proj_ty = _; proj = _; consumed = _; borrows })
      when borrows = [] -> false
    | ALoan (AEndedMutLoan { child; given_back = _; given_back_meta = _ })
      when is_aignored child.value -> false
    | _ -> true
  in
  let left_avalues =
    let avalues = List.filter keep_avalue abs0.avalues in
    ref avalues
  in
  let right_avalues = ref [] in

  (* Some preprocessing: save all the normalized types of the loan projectors in
     the left abstraction *)
  let left_norm_proj_loans = ref MarkedNormSymbProjSet.empty in
  List.iter
    (fun (av : tavalue) ->
      match av.value with
      | ASymbolic (pm, aproj) -> (
          match aproj with
          | AProjLoans { proj; consumed; borrows } ->
              [%sanity_check] span (consumed = []);
              [%sanity_check] span (borrows = []);
              let norm_proj_ty =
                normalize_proj_ty abs0.regions.owned proj.proj_ty
              in
              left_norm_proj_loans :=
                MarkedNormSymbProjSet.add
                  { pm; sv_id = proj.sv_id; norm_proj_ty }
                  !left_norm_proj_loans
          | _ -> ())
      | _ -> ())
    abs0.avalues;

  let push_right_avalue (av : tavalue) : unit =
    right_avalues := av :: !right_avalues
  in

  let rec add_avalue (av : tavalue) : unit =
    match av.value with
    | ALoan lc -> (
        match lc with
        | AMutLoan _ | ASharedLoan _ ->
            (* We simply add the value: we only merge loans coming from the *left*
              (this one comes from the right) with borrows coming from the *right*. *)
            push_right_avalue av
        | AEndedMutLoan { child; given_back; given_back_meta = _ } ->
            add_avalue child;
            add_avalue given_back
        | AEndedSharedLoan (sv, child) ->
            (* For now, we treat the case where there are no loans/borrows in the shared
             value, allowing us to eliminate it altogether. *)
            [%cassert] span
              (not (tvalue_has_loans_or_borrows (Some span) ctx sv))
              "Unimplemented";
            add_avalue child
        | AIgnoredMutLoan _ -> [%craise] span "Unimplemented"
        | AEndedIgnoredMutLoan { child; given_back; given_back_meta = _ } ->
            add_avalue child;
            add_avalue given_back
        | AIgnoredSharedLoan child -> add_avalue child)
    | ABorrow bc ->
        (* We may need to merge it *)
        begin
          match bc with
          | AMutBorrow (pm, bid, child) ->
              [%sanity_check] span (is_aignored child.value);
              let rec merge (avl : tavalue list) : tavalue list * bool =
                match avl with
                | [] -> ([], true)
                | av :: avl -> (
                    match av.value with
                    | ALoan (AMutLoan (pm', bid', _))
                      when pm = pm' && bid = bid' -> (avl, false)
                    | _ ->
                        let avl, keep = merge avl in
                        (av :: avl, keep))
              in
              let avalues, keep = merge !left_avalues in
              left_avalues := avalues;
              if keep then push_right_avalue av else ()
          | ASharedBorrow (pm, bid, _) ->
              let rec keep (avl : tavalue list) : bool =
                match avl with
                | [] -> true
                | av :: avl -> (
                    match av.value with
                    | ALoan (ASharedLoan (pm', bid', _, _))
                      when pm = pm' && bid = bid' -> false
                    | _ -> keep avl)
              in
              let keep = keep !left_avalues in
              if keep then push_right_avalue av else ()
          | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
              add_avalue given_back;
              add_avalue child
          | AIgnoredMutBorrow _
          | AEndedMutBorrow _
          | AEndedSharedBorrow
          | AProjSharedBorrow _ ->
              [%ltrace "Unexpected avalue: " ^ tavalue_to_string ctx av];
              [%craise] span "Unreachable"
        end
    | ASymbolic (pm, proj) -> begin
        match proj with
        | AProjLoans _ ->
            (* We simply add the value: we only merge loans coming from the *left*
               (this one comes from the right) with borrows coming from the *right*. *)
            push_right_avalue av
        | AProjBorrows { proj; loans } ->
            [%sanity_check] span (loans = []);
            (* Check if we need to eliminate it *)
            let norm_proj_ty =
              normalize_proj_ty abs1.regions.owned proj.proj_ty
            in
            if
              MarkedNormSymbProjSet.mem
                { pm; sv_id = proj.sv_id; norm_proj_ty }
                !left_norm_proj_loans
            then
              (* Eliminate: we need to filter the left avalues to remove the loan projector *)
              left_avalues :=
                List.filter
                  (fun (av : tavalue) ->
                    match av.value with
                    | ASymbolic (pm', proj') -> (
                        match proj' with
                        | AProjLoans { proj = proj'; _ } ->
                            if
                              proj'.sv_id = proj.sv_id && pm' = pm
                              && normalize_proj_ty abs0.regions.owned
                                   proj'.proj_ty
                                 = norm_proj_ty
                            then false
                            else true
                        | _ -> true)
                    | _ -> true)
                  !left_avalues
            else
              (* Do not eliminate *)
              push_right_avalue av
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            [%craise] span
              ("Internal error: please file an issue.\nUnexpected value: "
             ^ tavalue_to_string ctx av)
      end
    | AAdt { borrow_proj = _; variant_id = _; fields } ->
        (* Simply recurse *)
        List.iter add_avalue fields
    | AIgnored _ -> (* Nothing to register *) ()
  in
  List.iter add_avalue (List.filter keep_avalue abs1.avalues);

  (* We are done *)
  !left_avalues @ List.rev !right_avalues

(** Joining two analysis owners can unite disjoint pieces of one shared
    projection. The unchanged full type then describes their exact union in
    the resulting owned set. Recognize only the two original top-level nodes:
    no returned history, continuation, or newly split branch copy is admitted.
    Every unrelated node must retain its original ownership mask. *)
let shared_borrow_mask_union_pair span (ctx : eval_ctx) owned original_owners
    (first : tavalue) (second : tavalue) =
  match original_owners, first.value, second.value with
  | [left;right], ASymbolic (pm,AProjBorrows a),
      ASymbolic (other_pm,AProjBorrows b)
    when InterpPacketRouting.enabled () && first != second && pm <> PNone && pm = other_pm
      && a.loans = [] && b.loans = [] && a.proj.sv_id = b.proj.sv_id
      && equal_ty first.ty a.proj.proj_ty && equal_ty second.ty b.proj.proj_ty
      && equal_ty first.ty second.ty ->
      let original owner value = List.length (List.filter (( == ) value) owner.avalues) = 1 in
      let owners =
        if original left first && original right second then Some (left,right)
        else if original right first && original left second then Some (right,left)
        else None in
      (match owners with
      | None -> false
      | Some (left,right) ->
          let eligible owner = owner.can_end && Option.is_none owner.cont
            && AbsId.Set.is_empty owner.parents && AbsLevelSet.is_empty owner.ended_subabs in
          let matching_roots = List.filter (fun (value:tavalue) -> match value.value with
            | ASymbolic (marker,AProjBorrows p) -> marker=pm && p.proj.sv_id=a.proj.sv_id
            | _ -> false) (left.avalues @ right.avalues) in
          let ty = a.proj.proj_ty in
          let info = TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos ty in
          let regions = TypesUtils.ty_regions ty in
          let left_mask = RegionId.Set.inter regions left.regions.owned
          and right_mask = RegionId.Set.inter regions right.regions.owned in
          let result_mask = RegionId.Set.inter regions owned in
          if not (left.abs_id <> right.abs_id && eligible left && eligible right
            && List.length matching_roots = 2
            && not info.contains_mut_borrow && not info.contains_static
            && not (TypesUtils.ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos ty)
            && RegionId.Set.is_empty (RegionId.Set.inter regions ctx.ended_regions)
            && RegionId.Set.equal owned (RegionId.Set.union left.regions.owned right.regions.owned)
            && not (RegionId.Set.is_empty left_mask) && not (RegionId.Set.is_empty right_mask)
            && not (projections_intersect span ctx left.regions.owned ty right.regions.owned ty)
            && RegionId.Set.equal result_mask (RegionId.Set.union left_mask right_mask))
          then false
          else begin
            let module P = InterpPacketInterface in
            let pc = P.context_of_eval ctx in
            List.iter (fun (owner,selected) ->
              let rest = {owner with avalues=List.filter (fun value -> value != selected) owner.avalues} in
              try ignore (InterpPacketMerge.check_union_masks pc (P.describe_owner pc rest) owned)
              with InterpPacketMerge.Unsupported reason ->
                InterpPacketRouting.reject span ("shared borrow mask union: " ^ reason))
              [left,first;right,second];
            true
          end)
  | _ -> false

(** Auxiliary function for {!merge_abstractions}.

    Phase 2 of the merge: we remove markers, by merging pairs of the same
    element with different markers into one element without markers.

    Example:
    {[
      |MB l0|, MB l1, ︙MB l0︙
           ~~>
      MB l0, MB l1
    ]} *)
let merge_abstractions_merge_markers ?(original_owners = []) (span : Meta.span)
    (merge_funs : merge_duplicates_funcs) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : tavalue list) : tavalue list =
  [%ltrace
    "- avalues:\n"
    ^ String.concat ", " (List.map (tavalue_to_string ctx) avalues)];

  (* We simply iterate through the list of avalues create during the first phase,
     and progressively add them back: if we find a value with a complementary marker,
     we merge the values together, otherwise we add it to the list of values. *)
  let complementary_markers pm0 pm1 =
    (pm0 = PLeft && pm1 = PRight) || (pm0 = PRight && pm1 = PLeft)
  in

  (* Some utility functions *)
  (* Merge two aborrow contents - return [Some] if they were merged into a single value,
     return [None] otherwise.
   *)
  let try_merge_aborrow_contents (ty0 : rty) (bc0 : aborrow_content) (ty1 : rty)
      (bc1 : aborrow_content) : tavalue option =
    match (bc0, bc1) with
    | AMutBorrow (pm0, id0, child0), AMutBorrow (pm1, id1, child1)
      when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        Some (merge_funs.merge_amut_borrows id0 ty0 pm0 child0 ty1 pm1 child1)
    | ASharedBorrow (pm0, id0, sid0), ASharedBorrow (pm1, id1, sid1)
      when id0 = id1 ->
        if !Config.multi_exit_loops && pm0 = pm1 && pm0 <> PNone
           && sid0 <> sid1 && erase_regions ty0 = erase_regions ty1
        then
          (* These are distinct shared permissions from the same side, not
             complementary copies of one join output. Keep both records,
             including their original region types and shared-borrow IDs.
             Returning None lets add_avalue retain each value unchanged. *)
          None
        else (
          [%sanity_check] span (complementary_markers pm0 pm1);
          Some (merge_funs.merge_ashared_borrows id0 ty0 pm0 sid0 ty1 pm1 sid1))
    | _ ->
        (* Nothing to merge *)
        None
  in

  let try_merge_aloan_contents (ty0 : rty) (lc0 : aloan_content) (ty1 : rty)
      (lc1 : aloan_content) : tavalue option =
    [%ldebug
      "- lc0: "
      ^ aloan_content_to_string ctx lc0
      ^ "\n- lc1: "
      ^ aloan_content_to_string ctx lc1];
    match (lc0, lc1) with
    | AMutLoan (pm0, id0, child0), AMutLoan (pm1, id1, child1) when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some (merge_funs.merge_amut_loans id0 ty0 pm0 child0 ty1 pm1 child1)
    | ASharedLoan (pm0, id0, sv0, child0), ASharedLoan (pm1, id1, sv1, child1)
      when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some
          (merge_funs.merge_ashared_loans id0 ty0 pm0 sv0 child0 ty1 pm1 sv1
             child1)
    | _ ->
        (* Nothing to merge *)
        None
  in

  let try_merge_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : tavalue option =
    let check_complementary () =
      if not (complementary_markers pm0 pm1) then
        Printf.eprintf
          "PROJECTOR_MARKER_MERGE_REJECTED owned=%s\nfirst: %s\nsecond: %s\noriginal owners:\n%s\nall phase-2 values:\n%s\n%!"
          (RegionId.Set.to_string None owned_regions)
          (show_tavalue {ty=ty0;value=ASymbolic(pm0,proj0)})
          (show_tavalue {ty=ty1;value=ASymbolic(pm1,proj1)})
          (String.concat "\n" (List.map (abs_to_string span ~with_ended:true ctx) original_owners))
          (String.concat "\n" (List.map show_tavalue avalues));
      [%sanity_check] span (complementary_markers pm0 pm1)
    in
    match (proj0, proj1) with
    | AProjBorrows proj0, AProjBorrows proj1
      when proj0.proj.sv_id = proj1.proj.sv_id
           && projections_intersect span ctx owned_regions proj0.proj.proj_ty
                owned_regions proj1.proj.proj_ty ->
        check_complementary ();
        (* Merge *)
        Some (merge_funs.merge_aborrow_projs ty0 pm0 proj0 ty1 pm1 proj1)
    | AProjLoans proj0, AProjLoans proj1
      when proj0.proj.sv_id = proj1.proj.sv_id
           && projections_intersect span ctx owned_regions proj0.proj.proj_ty
                owned_regions proj1.proj.proj_ty ->
        check_complementary ();
        (* Merge *)
        Some (merge_funs.merge_aloan_projs ty0 pm0 proj0 ty1 pm1 proj1)
    | _ ->
        (* Nothing to merge *)
        None
  in

  (* Attempt to merge two avalues, if they are mergeable.

     Return [Some] with the result of the merge if it occurred, and [None]
     if the two values can't be merged (because they are of two different
     kinds for instance). *)
  let try_merge_avalues (av0 : tavalue) (av1 : tavalue) : tavalue option =
    if shared_borrow_mask_union_pair span ctx owned_regions original_owners av0 av1 then
      (* The result owns both disjoint source masks. Keep an exact original
         node and its same-side marker, without invoking the complementary
         branch callback, which would erase that marker. *)
      Some av0
    else match (av0.value, av1.value) with
    | ALoan c0, ALoan c1 -> try_merge_aloan_contents av0.ty c0 av1.ty c1
    | ABorrow c0, ABorrow c1 -> try_merge_aborrow_contents av0.ty c0 av1.ty c1
    | ASymbolic (pm0, proj0), ASymbolic (pm1, proj1) ->
        try_merge_projs (av0.ty, pm0, proj0) (av1.ty, pm1, proj1)
    | _ -> None
  in

  let merged = ref [] in
  let add_avalue (av : tavalue) : unit =
    let rec add avl =
      match avl with
      | [] -> [ av ]
      | av' :: avl -> (
          match try_merge_avalues av av' with
          | None ->
              (* No merge: continue *)
              av' :: add avl
          | Some av'' ->
              (* The two values were merged together: introduce the merged value
               and stop the exploration *)
              av'' :: avl)
    in
    merged := add !merged
  in

  List.iter add_avalue avalues;

  (* We're done *)
  !merged

(** Information about a borrow which is output by a continuation and which was
    bound in a let binding.

    We distinguish different cases, depending on whether the borrow has a marker
    or not. *)
type bound_borrow = (proj_marker * AbsFVarId.id * ty) list

(** Similar to [bound_borrow] but for symbolic projections *)
type bound_symbolic = (proj_marker * norm_proj_ty * AbsFVarId.id * ty) list

type bound_inputs_outputs = {
  borrows : bound_borrow BorrowId.Map.t;
  symbolic : bound_symbolic SymbolicValueId.Map.t;
  all_bindings : (BorrowId.id, SymbolicValueId.id) Either.t list;
      (** We use this to remember the order in which values were inserted: we
          use this to properly order the outputs of the composed continuation.

          Note that as we do not store the projectors and as we allow removing
          values from the maps above, the values in [all_bindings] may contain
          duplicates, or may contain values which are not actually bound anymore
          (this is fine, because we only use this list to give us an order). *)
  input_loans : (AbsFVarId.id * proj_marker list * ty) BorrowId.Map.t;
      (** Map from an input loan id to:
          - the free variable introduced to re-bind it
          - the list of projection markers encountered in the merged
            continuations (we collect the list of projection markers to compute
            their union: the merged continuation will use the union) *)
  input_symbolic :
    (AbsFVarId.id * proj_marker list * norm_proj_ty * ty) SymbolicValueId.Map.t;
      (** Similar to [input_symbolic] *)
  all_input_bindings : (BorrowId.id, SymbolicValueId.id) Either.t list;
      (** Same purpose as [all_bindings], but for the inputs *)
}

let bound_borrow_to_string ((bid, b) : BorrowId.id * bound_borrow) : string =
  Print.list_to_string
    (fun (pm, fid, _ty) ->
      "fv@" ^ AbsFVarId.to_string fid ^ " <- "
      ^ Print.Values.add_proj_marker pm ("l@" ^ BorrowId.to_string bid))
    b

let bound_symbolic_to_string (ctx : eval_ctx)
    ((sid, b) : SymbolicValueId.id * bound_symbolic) : string =
  Print.list_to_string
    (fun (pm, norm_proj_ty, fid, _ty) ->
      "fv@" ^ AbsFVarId.to_string fid ^ " <- "
      ^ Print.Values.add_proj_marker pm
          ("s@"
          ^ SymbolicValueId.to_string sid
          ^ " <: "
          ^ ty_to_string ctx norm_proj_ty))
    b

let input_loan_to_string
    ((bid, (fid, pml, _ty)) :
      BorrowId.id * (AbsFVarId.id * proj_marker list * ty)) : string =
  let bid = BorrowId.to_string bid in
  "fv@" ^ AbsFVarId.to_string fid ^ " <- "
  ^ Print.list_to_string (fun pm -> Print.Values.add_proj_marker pm bid) pml

let input_symbolic_to_string (ctx : eval_ctx)
    ((sid, (fid, pml, norm_proj_ty, _ty)) :
      SymbolicValueId.id * (AbsFVarId.id * proj_marker list * norm_proj_ty * ty))
    : string =
  let sv =
    "s@"
    ^ SymbolicValueId.to_string sid
    ^ " <: "
    ^ ty_to_string ctx norm_proj_ty
  in
  "fv@" ^ AbsFVarId.to_string fid ^ " <- "
  ^ Print.list_to_string (fun pm -> Print.Values.add_proj_marker pm sv) pml

let bound_inputs_outputs_to_string (ctx : eval_ctx) (b : bound_inputs_outputs) :
    string =
  let {
    borrows;
    symbolic;
    all_bindings;
    input_loans;
    input_symbolic;
    all_input_bindings;
  } =
    b
  in
  let bindings_to_string (bindings : (loan_id, symbolic_value_id) Either.t list)
      : string =
    Print.list_to_string
      (fun x ->
        match x with
        | Either.Left lid -> "l@" ^ BorrowId.to_string lid
        | Right sid -> "s@" ^ SymbolicValueId.to_string sid)
      bindings
  in
  "{\n  borrows: "
  ^ Print.list_to_string bound_borrow_to_string (BorrowId.Map.bindings borrows)
  ^ "\n  symbolic: "
  ^ Print.list_to_string
      (bound_symbolic_to_string ctx)
      (SymbolicValueId.Map.bindings symbolic)
  ^ "\n  all_bindings: "
  ^ bindings_to_string all_bindings
  ^ "\n  input_loans: "
  ^ Print.list_to_string input_loan_to_string
      (BorrowId.Map.bindings input_loans)
  ^ "\n  input_symbolic: "
  ^ Print.list_to_string
      (input_symbolic_to_string ctx)
      (SymbolicValueId.Map.bindings input_symbolic)
  ^ "\n  input_bindings: "
  ^ bindings_to_string all_input_bindings
  ^ "\n}"

let bound_inputs_outputs_add_borrow (span : Meta.span) (bid : BorrowId.id)
    (pm : proj_marker) (fvid : AbsFVarId.id) (ty : ty)
    (out : bound_inputs_outputs) : bound_inputs_outputs =
  let borrow = (pm, fvid, ty) in
  let borrows =
    BorrowId.Map.update bid
      (fun bound ->
        match bound with
        | None -> Some [ borrow ]
        | Some bound ->
            [%sanity_check] span
              (List.for_all
                 (fun (pm', _, _) -> not (proj_markers_intersect pm pm'))
                 bound);
            Some (borrow :: bound))
      out.borrows
  in
  { out with borrows; all_bindings = Left bid :: out.all_bindings }

(** Given an input loan, consume a registered output borrow. If there is no such
    output borrow, register the input (it will be an input of the composed
    continuation. *)
let bound_inputs_outputs_update_input_loan (span : Meta.span)
    (bid : BorrowId.id) (ty : ty) (pm : proj_marker)
    (out : bound_inputs_outputs) : bound_inputs_outputs * tevalue =
  match BorrowId.Map.find_opt bid out.borrows with
  | None ->
      (* There is no corresponding input value: check if we already introduced a
       free variable for this loan (for a complementary projector), if not,
       introduce a fresh free variable *)
      let fid, input_loans =
        match BorrowId.Map.find_opt bid out.input_loans with
        | None ->
            let fid = fresh_abs_fvar_id () in
            (fid, BorrowId.Map.add bid (fid, [ pm ], ty) out.input_loans)
        | Some (fid, pml, ty') ->
            (fid, BorrowId.Map.add bid (fid, pm :: pml, ty') out.input_loans)
      in
      let v : tevalue = { value = EFVar fid; ty } in
      let out =
        {
          out with
          input_loans;
          all_input_bindings = Left bid :: out.all_input_bindings;
        }
      in
      (* *)
      (out, v)
  | Some bound ->
      (* There is a corresponding output value: consume it *)
      (* Filter the bound values which intersect the current proj marker *)
      let bound, bound' =
        List.partition (fun (pm', _, _) -> proj_markers_intersect pm pm') bound
      in
      let bound, value =
        match (pm, bound) with
        | PLeft, [ (PLeft, fvid, ty) ] -> ([], { value = EFVar fvid; ty })
        | PRight, [ (PRight, fvid, ty) ] -> ([], { value = EFVar fvid; ty })
        | PLeft, [ (PNone, fvid, ty) ] ->
            ([ (PRight, fvid, ty) ], { value = EFVar fvid; ty })
        | PRight, [ (PNone, fvid, ty) ] ->
            ([ (PLeft, fvid, ty) ], { value = EFVar fvid; ty })
        | PNone, [ (PNone, fvid, ty) ] -> ([], { value = EFVar fvid; ty })
        | ( PNone,
            ( [ (PLeft, fvidl, tyl); (PRight, fvidr, tyr) ]
            | [ (PRight, fvidr, tyr); (PLeft, fvidl, tyl) ] ) ) ->
            let lv : tevalue = { value = EFVar fvidl; ty = tyl } in
            let rv : tevalue = { value = EFVar fvidr; ty = tyr } in
            ([], { value = EJoinMarkers (lv, rv); ty = tyl })
        | _ ->
            [%ldebug
              "- pm: " ^ show_proj_marker pm ^ "\n- bound:\n"
              ^ bound_borrow_to_string (bid, bound)];
            [%internal_error] span
      in
      let out =
        let bound =
          match bound @ bound' with
          | [] -> None
          | l -> Some l
        in
        {
          out with
          borrows = BorrowId.Map.update bid (fun _ -> bound) out.borrows;
        }
      in
      (out, value)

let bound_inputs_outputs_add_symbolic (sid : SymbolicValueId.id)
    (pm : proj_marker) (proj_ty : norm_proj_ty) (fvid : AbsFVarId.id) (ty : ty)
    (out : bound_inputs_outputs) : bound_inputs_outputs =
  let s = (pm, proj_ty, fvid, ty) in
  let symbolic =
    SymbolicValueId.Map.update sid
      (fun bound ->
        match bound with
        | None -> Some [ s ]
        | Some bound -> Some (s :: bound))
      out.symbolic
  in
  { out with symbolic; all_bindings = Right sid :: out.all_bindings }

let bound_inputs_outputs_update_input_symbolic (span : Meta.span)
    (ctx : eval_ctx) (sid : SymbolicValueId.id) (pm : proj_marker) (ty : ty)
    (proj_ty : norm_proj_ty) (out : bound_inputs_outputs) :
    bound_inputs_outputs * tevalue =
  match SymbolicValueId.Map.find_opt sid out.symbolic with
  | None ->
      (* There is no corresponding input value: check if we already introduced a
       free variable for this loan (for a complementary projector), if not,
       introduce a fresh free variable *)
      let fid, input_symbolic =
        match SymbolicValueId.Map.find_opt sid out.input_symbolic with
        | None ->
            let fid = fresh_abs_fvar_id () in
            ( fid,
              SymbolicValueId.Map.add sid (fid, [ pm ], proj_ty, ty)
                out.input_symbolic )
        | Some (fid, pml, proj_ty', ty') ->
            [%sanity_check] span (proj_ty = proj_ty');
            ( fid,
              SymbolicValueId.Map.add sid
                (fid, pm :: pml, proj_ty', ty')
                out.input_symbolic )
      in
      let v : tevalue = { value = EFVar fid; ty } in
      let out =
        {
          out with
          input_symbolic;
          all_input_bindings = Right sid :: out.all_input_bindings;
        }
      in
      (* *)
      (out, v)
  | Some bound ->
      (* There is a corresponding output value: consume it *)
      (* Filter the bound values which intersect the current proj marker and projection *)
      let bound, bound' =
        List.partition
          (fun (pm', proj_ty', _, _) ->
            proj_markers_intersect pm pm'
            && norm_proj_tys_intersect span ctx proj_ty proj_ty')
          bound
      in
      let bound, value =
        match (pm, bound) with
        | PLeft, [ (PLeft, proj_ty', fvid, ty) ] ->
            [%cassert] span (proj_ty' = proj_ty) "Unimplemented";
            ([], { value = EFVar fvid; ty })
        | PLeft, [ (PNone, proj_ty', fvid, ty) ] ->
            [%cassert] span (proj_ty' = proj_ty) "Unimplemented";
            ([ (PRight, proj_ty', fvid, ty) ], { value = EFVar fvid; ty })
        | PRight, [ (PRight, proj_ty', fvid, ty) ] ->
            [%cassert] span (proj_ty' = proj_ty) "Unimplemented";
            ([], { value = EFVar fvid; ty })
        | PRight, [ (PNone, proj_ty', fvid, ty) ] ->
            [%cassert] span (proj_ty' = proj_ty) "Unimplemented";
            ([ (PLeft, proj_ty', fvid, ty) ], { value = EFVar fvid; ty })
        | PNone, [ (PNone, proj_ty', fvid, ty') ] ->
            [%cassert] span (proj_ty' = proj_ty) "Unimplemented";
            ([], { value = EFVar fvid; ty = ty' })
        | ( PNone,
            ( [ (PLeft, proj_tyl, fvidl, tyl); (PRight, proj_tyr, fvidr, tyr) ]
            | [ (PRight, proj_tyr, fvidr, tyr); (PLeft, proj_tyl, fvidl, tyl) ]
              ) ) ->
            [%cassert] span (proj_tyl = proj_ty) "Unimplemented";
            [%cassert] span (proj_tyr = proj_ty) "Unimplemented";
            let lv : tevalue = { value = EFVar fvidl; ty = tyl } in
            let rv : tevalue = { value = EFVar fvidr; ty = tyr } in
            ([], { value = EJoinMarkers (lv, rv); ty = tyl })
        | _ -> [%internal_error] span
      in
      let out =
        let bound =
          match bound @ bound' with
          | [] -> None
          | l -> Some l
        in
        {
          out with
          symbolic =
            SymbolicValueId.Map.update sid (fun _ -> bound) out.symbolic;
        }
      in
      (out, value)

(** Bind the outputs from an abs continuation.

    See the documentation of [abs_cont].

    We return the pattern (derived from the output) and the updated input (we
    might have replaced some loans with free variables, in case the output of
    the corresponding borrows were bound elsewhere). *)
let bind_outputs_from_output_input (span : Meta.span) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (bound : bound_inputs_outputs ref)
    (output : tevalue) (input : tevalue) : tepat * tevalue =
  (* Update the input value by substituting expressions (such as a mutable loan)
     whose input have been bound earlier (because we bound an abstraction continuation
     earlier which has a mutable borrow corresponding to this mutable loan) *)
  let rec update_input (regions : RegionId.Set.t) (input : tevalue) : tevalue =
    match input.value with
    | ELet (regions', pat, bvalue, next) ->
        (* Explore the bound expression *)
        let bvalue = update_input regions bvalue in
        (* Open the pattern *)
        let pat, next = open_binder span pat next in
        (* Explore the inner expression *)
        let next = update_input regions' next in
        (* Close the let (and the binders) *)
        mk_let span regions' pat bvalue next
    | EJoinMarkers (left, right) ->
        let left = update_input regions left in
        let right = update_input regions right in
        { input with value = EJoinMarkers (left, right) }
    | EApp (f, args) ->
        let args = List.map (List.map (update_input regions)) args in
        { input with value = EApp (f, args) }
    | EFVar _ -> input
    | EBVar _ | EBottom ->
        (* Shouldn't get there. Note in particular that all the patterns should
           have been opened: we shouldn't find bound variables, only free variables. *)
        [%craise] span "Unreachable"
    | EAdt adt ->
        let fields = List.map (update_input regions) adt.fields in
        {
          value =
            EAdt
              {
                borrow_proj = adt.borrow_proj;
                variant_id = adt.variant_id;
                fields;
              };
          ty = input.ty;
        }
    | ELoan loan ->
        (* Check if this loan was previously bound *)
        begin
          match loan with
          | EMutLoan (pm, bid, child) ->
              [%cassert] span (is_eignored child.value) "Unimplemented";
              let bound', e =
                bound_inputs_outputs_update_input_loan span bid input.ty pm
                  !bound
              in
              bound := bound';
              e
          | EEndedMutLoan { child; given_back = _; given_back_meta = _ } ->
              [%cassert] span (is_eignored child.value) "Unimplemented";
              input
          | EIgnoredMutLoan (_lid, child) ->
              [%cassert] span (is_eignored child.value) "Unimplemented";
              input
          | EEndedIgnoredMutLoan { child; given_back = _; given_back_meta = _ }
            ->
              [%cassert] span (is_eignored child.value) "Unimplemented";
              input
        end
    | ESymbolic (pm, proj) -> begin
        match proj with
        | EProjLoans { proj; consumed; borrows } ->
            (* Not sure what to do in the following cases *)
            [%cassert] span (consumed = []) "Unimplemented";
            [%cassert] span (borrows = []) "Unimplemented";
            (* Check if this projection was previously bound *)
            let ty = proj.proj_ty in
            let norm_proj_ty = normalize_proj_ty regions ty in
            let bound', e =
              bound_inputs_outputs_update_input_symbolic span ctx proj.sv_id pm
                ty norm_proj_ty !bound
            in
            bound := bound';
            e
        | EEndedProjLoans { proj_ty = _; proj = _; consumed; borrows } ->
            [%cassert] span (consumed = []) "Unimplemented";
            [%cassert] span (borrows = []) "Unimplemented";
            input
        | EProjBorrows _ | EEndedProjBorrows _ ->
            [%craise] span "Nested borrows are not supported yet in this case"
        | EEmpty ->
            (* We shouldn't get here? *)
            [%craise] span "Unexpected"
      end
    | EBorrow _ ->
        [%craise] span "Nested borrows are not supported yet in this case"
    | EMutBorrowInput x ->
        { input with value = EMutBorrowInput (update_input regions x) }
    | EValue _ | EIgnored _ -> input
  in
  let rec bind_output (regions : RegionId.Set.t) (output : tevalue) : tepat =
    match output.value with
    | ELet _ | EJoinMarkers _ | EBVar _ | EFVar _ | EApp _ | EMutBorrowInput _
      ->
        (* Those expressions should not appear in the *output* expression
           (some of them might appear only in the *input* expression) *)
        [%craise] span ("Unexpected expression: " ^ tevalue_to_string ctx output)
    | EBottom ->
        (* We're not inside a loan or a borrow: simply ignore it *)
        { pat = PIgnored; ty = output.ty }
    | EAdt adt ->
        let pats = List.map (bind_output regions) adt.fields in
        { pat = PAdt (adt.variant_id, pats); ty = output.ty }
    | ELoan _ ->
        (* We shouldn't reach a loan which is not itself inside a borrow *)
        [%craise] span "Unexpected"
    | EBorrow borrow ->
        (* Two cases depending on whether we are inside a loan or not *)
        begin
          match borrow with
          | EMutBorrow (pm, bid, child) ->
              [%cassert] span (is_eignored child.value) "Unimplemented";
              (* Compute the binding pattern *)
              let fid = fresh_abs_fvar_id () in
              let pat : tepat = { pat = POpen fid; ty = output.ty } in
              (* We need to register the binding *)
              bound :=
                bound_inputs_outputs_add_borrow span bid pm fid output.ty !bound;
              (* *)
              pat
          | EEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
              (* For now we simply check that:
                 - the child and the given back values are ignored
                 - or the given back value consumes nothing

                 TODO: make more precise
              *)
              if is_eignored child.value && is_eignored given_back.value then
                { pat = PIgnored; ty = output.ty }
              else if
                not (ty_has_mut_borrows ctx.type_ctx.type_infos given_back.ty)
              then bind_output regions child
              else [%craise] span "Unimplemented"
          | EIgnoredMutBorrow _ -> [%craise] span "Unimplemented"
          | EEndedMutBorrow _ ->
              (* We shouldn't get there. If we find an ended borrow in a region
                 abstraction it means the abstraction was ended and thus removed
                 from the context: we shouldn't be in the process of merging it...
              *)
              [%craise] span "Unexpected"
        end
    | ESymbolic (pm, proj) ->
        (* If we get here it means the symbolic value gets projected (we can't ignore it) *)
        begin
          match proj with
          | EProjLoans _ | EEndedProjLoans _ ->
              (* We shouldn't reach a loan which is not itself inside a borrow *)
              [%craise] span "Unexpected"
          | EProjBorrows { proj; loans } ->
              [%sanity_check] span (loans = []);
              (* Compute the binding pattern *)
              let { sv_id; proj_ty } : esymbolic_proj = proj in
              [%sanity_check] span (loans = []);
              let fid = fresh_abs_fvar_id () in
              let pat : tepat = { pat = POpen fid; ty = output.ty } in
              (* We need to register the binding *)
              let norm_ty = normalize_proj_ty regions proj_ty in
              bound :=
                bound_inputs_outputs_add_symbolic sv_id pm norm_ty fid proj_ty
                  !bound;
              (* *)
              pat
          | EEndedProjBorrows _ ->
              (* Same remark as for the ended borrows above *)
              [%craise] span "Unexpected"
          | EEmpty ->
              (* We shouldn't get here? *)
              [%craise] span "Unexpected"
        end
    | EValue _ ->
        (* We're not inside a loan or a borrow: simply ignore it *)
        { pat = PIgnored; ty = output.ty }
    | EIgnored _ ->
        (* We're not inside a loan or a borrow: simply ignore it *)
        { pat = PIgnored; ty = output.ty }
  in
  let input = update_input regions input in
  let pat = bind_output regions output in
  (pat, input)

let tevalue_get_max_level (v : tevalue) : int =
  let max_level = ref (-1) in
  let visitor =
    (* We count the ended loans: we want to decompose if we see something like this
       (the loan in the given back sub-value was ended):
       {[
         @ended_ignored_mut_borrow{
           child: (s@37 <: core::slice::iter::IterMut<'23, u16>);
           given_back: ended_eproj_loans) :=
         FunCall(abs_id@43)[...]
       ]}
     *)
    InterpBorrowsCore.get_max_sub_abs_visitor ~with_evalues:true
      ~with_ended:true max_level
  in
  visitor#visit_tevalue 0 v;
  !max_level

let project_output_at_level span (level : int) (v : tevalue) : tevalue =
  let rec project level (v : tevalue) : tevalue =
    let stop (v : tevalue) =
      if level = 0 then v else { v with value = EIgnored None }
    in
    match v.value with
    | ELet _ | EJoinMarkers _ | EBVar _ | EApp _ ->
        [%craise] span "Unimplemented"
    | EAdt { borrow_proj; variant_id; fields } ->
        let fields = List.map (project level) fields in
        { v with value = EAdt { borrow_proj; variant_id; fields } }
    | ELoan lc -> (
        match lc with
        | EMutLoan (pm, lid, child) ->
            let child = project level child in
            if level = 0 then
              { v with value = ELoan (EMutLoan (pm, lid, child)) }
            else child
        | EEndedMutLoan { child; given_back; given_back_meta = _ } ->
            if level = 0 then project level child
            else project (level - 1) given_back
        | EIgnoredMutLoan _ -> [%craise] span "Unimplemented"
        | EEndedIgnoredMutLoan { child; given_back; given_back_meta = _ } ->
            if level = 0 then project level child
            else project (level - 1) given_back)
    | EBorrow bc -> (
        match bc with
        | EMutBorrow (pm, bid, child) ->
            let child = project level child in
            if level = 0 then
              { v with value = EBorrow (EMutBorrow (pm, bid, child)) }
            else child
        | EIgnoredMutBorrow _ -> [%craise] span "Unimplemented"
        | EEndedMutBorrow (mv, child) ->
            let child = project level child in
            if level = 0 then
              { v with value = EBorrow (EEndedMutBorrow (mv, child)) }
            else child
        | EEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
            if level = 0 then project level child
            else project (level - 1) given_back)
    | ESymbolic (_pm, proj) -> (
        match proj with
        | EProjLoans { proj = _; consumed; borrows } ->
            [%cassert] span (consumed = []) "Unimplemented";
            [%cassert] span (borrows = []) "Unimplemented";
            stop v
        | EProjBorrows { proj = _; loans } ->
            [%cassert] span (loans = []) "Unimplemented";
            stop v
        | EEndedProjLoans { proj_ty = _; proj = _; consumed; borrows } ->
            [%cassert] span (consumed = []) "Unimplemented";
            [%cassert] span (borrows = []) "Unimplemented";
            stop v
        | EEndedProjBorrows { proj_ty = _; mvalues = _; loans } ->
            [%cassert] span (loans = []) "Unimplemented";
            stop v
        | EEmpty -> stop v)
    | EFVar _ | EValue _ | EIgnored _ -> stop v
    | EMutBorrowInput _ | EBottom -> [%craise] span "Unreachable"
  in
  project level v

(** Small trick to handle nested borrows.

    Considering the code below:
    {[
      struct IterMut<'a, T> {
          v : Option<&'a mut T>,
      }

      impl<'a, T> IterMut<'a, T> {
          fn next(&mut self) -> Option<&'a mut T>
      }

      fn iter_mut_loop<'a, T>(mut x : IterMut<'a, T>) {
          while let Some(_) = x.next() {}
      }
    ]}

    In the loop, after ending the outer lifetime we get an abstraction like this
    for the inner lifetime:
    {[
      @ended_ignored_mut_borrow((s@2 <: IterMut<'1, T>); ⌊s@3 <: IterMut<'1, T>⌋) :=
        FunCall(...)[(Some ⌊s@1 <: &'1 mut T⌋)]
    ]}

    We restructure it to:
    {[
      (s@2 <: IterMut<'1, T>) :=
        FunCall(...)[(⌊s@3 <: IterMut<'1, T>⌋); (Some ⌊s@1 <: &'1 mut T⌋)]
    ]}

    TODO: generalize to an arbitrary number of nestings and arbitrary relations
    input/output *)

(** Set [borrow_proj] to the given value in all [EAdt] nodes of a tevalue. *)
let rec tevalue_set_borrow_proj (bp : bool) (v : tevalue) : tevalue =
  match v.value with
  | EAdt { borrow_proj = _; variant_id; fields } ->
      let fields = List.map (tevalue_set_borrow_proj bp) fields in
      { v with value = EAdt { borrow_proj = bp; variant_id; fields } }
  | _ -> v

let abs_cont_destructure_input_output_levels (span : Meta.span) (ctx : eval_ctx)
    (output : tevalue) (input : tevalue) : tevalue * tevalue =
  (* Check if the input is a function call *)
  match input.value with
  | EApp (EFunCall abs_id, args) ->
      (* Check the number of levels in the output: it should be <= 1 and we do
       the modification only if it is exactly 1 *)
      let max_level = tevalue_get_max_level output in
      if max_level <= 0 then (
        [%ltrace
          "not decomposing nested borrows: max level is "
          ^ string_of_int max_level];
        (* Keep it as it is *)
        (output, input))
      else (
        [%ltrace
          "decomposing nested borrows:\n- output:\n"
          ^ tevalue_to_string ctx output
          ^ "\n- input:\n"
          ^ tevalue_to_string ctx input];

        (* Decompose *)
        [%cassert] span (max_level = 1) "Unreachable";

        let input1 = project_output_at_level span 1 output in
        (* input1 was extracted from the borrow output but becomes a loan input:
           flip borrow_proj to false *)
        let input1 = tevalue_set_borrow_proj false input1 in
        let output = project_output_at_level span 0 output in
        [%ltrace
          "- input1:\n"
          ^ tevalue_to_string ctx input1
          ^ "\n- input:\n"
          ^ Print.list_to_string
              (Print.list_to_string (tevalue_to_string ctx))
              args
          ^ "\n- output:\n"
          ^ tevalue_to_string ctx output];

        let input =
          { input with value = EApp (EFunCall abs_id, [ input1 ] :: args) }
        in
        (output, input))
  | _ ->
      [%ltrace
        "not decomposing nested borrows: the input is not a function call"];
      (output, input)

let abs_cont_bind_outputs (span : Meta.span) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (bound : bound_inputs_outputs ref)
    (cont : abs_cont) : tepat * tevalue =
  match (cont.output, cont.input) with
  | Some output, Some input ->
      let output, input =
        abs_cont_destructure_input_output_levels span ctx output input
      in
      bind_outputs_from_output_input span ctx regions bound output input
  | _ -> [%craise] span "Unreachable"

(** Create the output of a composed continuation, and its corresponding input
    expression (without the let-bindings).

    We simply list all the bound outputs which were not consumed (the free
    variables give us the inputs, and the borrow themselves give us the outputs)
    by following the order in which they were added to the map. *)
let merge_abs_conts_generate_output (span : Meta.span) (_ctx : eval_ctx)
    (all_bindings : (BorrowId.id, SymbolicValueId.id) Either.t list)
    (bound : bound_inputs_outputs) : tevalue * tevalue =
  let bindings = all_bindings in
  let borrows = ref bound.borrows in
  let symbolic = ref bound.symbolic in
  let outputs = ref [] in
  let inputs = ref [] in

  let add_output_binding (binding : (BorrowId.id, SymbolicValueId.id) Either.t)
      =
    match binding with
    | Left bid -> begin
        match BorrowId.Map.find_opt bid !borrows with
        | None -> ()
        | Some values ->
            let (output, input) : tevalue * tevalue =
              match values with
              | [ (pm, fid, ty) ] ->
                  let output : tevalue =
                    {
                      value =
                        EBorrow (EMutBorrow (pm, bid, mk_eignored None ty));
                      ty;
                    }
                  in
                  let input : tevalue = { value = EFVar fid; ty } in
                  (output, input)
              | [ (PLeft, fidl, tyl); (PRight, fidr, tyr) ]
              | [ (PRight, fidr, tyr); (PLeft, fidl, tyl) ] ->
                  let inputl : tevalue = { value = EFVar fidl; ty = tyl } in
                  let inputr : tevalue = { value = EFVar fidr; ty = tyr } in
                  let input : tevalue =
                    { value = EJoinMarkers (inputl, inputr); ty = tyl }
                  in
                  let output =
                    {
                      value =
                        EBorrow (EMutBorrow (PNone, bid, mk_eignored None tyl));
                      ty = tyl;
                    }
                  in
                  (output, input)
              | _ -> [%internal_error] span
            in
            borrows := BorrowId.Map.remove bid !borrows;
            outputs := output :: !outputs;
            inputs := input :: !inputs
      end
    | Right sv_id -> begin
        match SymbolicValueId.Map.find_opt sv_id !symbolic with
        | None -> ()
        | Some values ->
            let (output, input) : tevalue * tevalue =
              match values with
              | [ (pm, _norm_proj_ty, fid, ty) ] ->
                  let input : tevalue = { value = EFVar fid; ty } in
                  let output : tevalue =
                    {
                      value =
                        ESymbolic
                          ( pm,
                            EProjBorrows
                              { proj = { sv_id; proj_ty = ty }; loans = [] } );
                      ty;
                    }
                  in
                  (output, input)
              | [ (PLeft, proj_tyl, fidl, tyl); (PRight, proj_tyr, fidr, tyr) ]
              | [ (PRight, proj_tyr, fidr, tyr); (PLeft, proj_tyl, fidl, tyl) ]
                ->
                  [%sanity_check] span (proj_tyl = proj_tyr);
                  let inputl : tevalue = { value = EFVar fidl; ty = tyl } in
                  let inputr : tevalue = { value = EFVar fidr; ty = tyr } in
                  let input : tevalue =
                    { value = EJoinMarkers (inputl, inputr); ty = tyl }
                  in
                  let output : tevalue =
                    {
                      value =
                        ESymbolic
                          ( PNone,
                            EProjBorrows
                              { proj = { sv_id; proj_ty = tyl }; loans = [] } );
                      ty = tyl;
                    }
                  in
                  (output, input)
              | _ -> [%internal_error] span
            in
            symbolic := SymbolicValueId.Map.remove sv_id !symbolic;
            outputs := output :: !outputs;
            inputs := input :: !inputs
      end
  in
  List.iter add_output_binding bindings;
  let input = mk_etuple ~borrow_proj:false (List.rev !inputs) in
  let output = mk_etuple ~borrow_proj:true (List.rev !outputs) in
  (output, input)

(** Create the input binding all inputs of a composed continuation. *)
let merge_abs_conts_generate_input (span : Meta.span) (ctx : eval_ctx)
    (all_bindings : (BorrowId.id, SymbolicValueId.id) Either.t list)
    (bound : bound_inputs_outputs) : tepat * tevalue =
  let bindings = all_bindings in
  let loans = ref bound.input_loans in
  let symbolic = ref bound.input_symbolic in
  let pats = ref [] in
  let inputs = ref [] in

  let add_input_binding (binding : (BorrowId.id, SymbolicValueId.id) Either.t) =
    match binding with
    | Left bid -> begin
        match BorrowId.Map.find_opt bid !loans with
        | None -> ()
        | Some (fid, pml, ty) ->
            let pm =
              match pml with
              | [ pm ] -> pm
              | [ PLeft; PRight ] | [ PRight; PLeft ] -> PNone
              | _ -> [%internal_error] span
            in
            let pat : tepat = { pat = POpen fid; ty } in
            let input : tevalue =
              { value = ELoan (EMutLoan (pm, bid, mk_eignored None ty)); ty }
            in
            loans := BorrowId.Map.remove bid !loans;
            pats := pat :: !pats;
            inputs := input :: !inputs
      end
    | Right sv_id -> begin
        match SymbolicValueId.Map.find_opt sv_id !symbolic with
        | None -> ()
        | Some ((fid, pml, _, ty) as bsymb) ->
            let pm =
              match pml with
              | [ pm ] -> pm
              | [ PLeft; PRight ] | [ PRight; PLeft ] -> PNone
              | _ ->
                  [%ldebug
                    "Unexpected:\n" ^ input_symbolic_to_string ctx (sv_id, bsymb)];
                  [%internal_error] span
            in
            let pat : tepat = { pat = POpen fid; ty } in
            let input : tevalue =
              {
                value =
                  ESymbolic
                    ( pm,
                      EProjLoans
                        {
                          proj = { sv_id; proj_ty = ty };
                          consumed = [];
                          borrows = [];
                        } );
                ty;
              }
            in
            symbolic := SymbolicValueId.Map.remove sv_id !symbolic;
            pats := pat :: !pats;
            inputs := input :: !inputs
      end
  in
  List.iter add_input_binding bindings;
  let pat = mk_epat_tuple (List.rev !pats) in
  let input = mk_etuple ~borrow_proj:false (List.rev !inputs) in
  (pat, input)

(** Merge two abstraction continuations.

    We merge from the right to the left, i.e.: we merge the (input) loans from
    [abs0] with the (output) borrows from [abs1]. *)
let merge_abs_conts_aux (span : Meta.span) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) (cont0 : abs_cont) (cont1 : abs_cont) : abs_cont =
  [%ltrace
    "- cont0:\n  "
    ^ abs_cont_to_string span ctx ~indent:"  " cont0
    ^ "\n- cont1:\n  "
    ^ abs_cont_to_string span ctx ~indent:"  " cont1];

  (* The way we proceed is simple.

     Let's say we want to merge A1 into A0:
     {[
       A0 { MB l0, ML l1 } ⟦ MB l0 = ML l1 ⟧
       A1 { MB l1, MB l2, ML l3 } ⟦ (MB l1, MB l2) = if b then (ML l3, 1) else (0, ML l3) ⟧
     ]}

     We first bind all the output values of the continuation in A1 like so:
     {[
       let (v_l1, v_l2) = if b then (ML l3, 1) else (0, ML l3) in
     ]}

     We then update the continuation in A0 to substitute the loans (they are inputs)
     whose corresponding borrows are outputs of the continuation of A1, and bind the outputs
     of A0. It gives:
     {[
       let v_l0 = v_l1 in
     ]}

     We output all the outputs of A1 which are not "consumed" by inputs of A0,
     as well as all the outputs of A0:
     {[
       (v_l0, v_l2)
     ]}

     Finally, we introduce binders for the remaining inputs of *both* continuations.
     This allows us to control the order in which those inputs appear (this is
     important for the translation, because it has an effect on the type of the
     translated continuation).

     The final, composed continuation is:
     {[
       (MB l0, MB l2) =
         let v0 = ML l3 in
         let (v_l1, v_l2) = if b then (v0, 1) else (0, v0) in
         let v_l0 = v_l1 in
         (v_l0, v_l2)
     ]}
  *)

  (* Initialize the map containing the bound outputs *)
  let bound : bound_inputs_outputs =
    {
      borrows = BorrowId.Map.empty;
      symbolic = SymbolicValueId.Map.empty;
      all_bindings = [];
      input_loans = BorrowId.Map.empty;
      input_symbolic = SymbolicValueId.Map.empty;
      all_input_bindings = [];
    }
  in
  let bound = ref bound in

  (* Introduce binders for all the inputs of the second continuation *)

  (* Bind all the outputs of the second continuation *)
  let pat1, inputs1 =
    abs_cont_bind_outputs span ctx abs1.regions.owned bound cont1
  in
  let bindings1 = !bound.all_bindings in
  let input_bindings1 = !bound.all_input_bindings in
  [%ltrace
    "- pat1: " ^ tepat_to_string ctx pat1 ^ "\n- inputs1: "
    ^ tevalue_to_string ctx inputs1
    ^ "\n- bound_inputs_outputs:\n"
    ^ bound_inputs_outputs_to_string ctx !bound];

  (* For the final order to be correct, because we bind the second continuation
     then the first, we need to reset the [all_bindings] field *)
  bound := { !bound with all_bindings = []; all_input_bindings = [] };

  (* Next, bind the outputs of the first continuation, while updating its inputs *)
  let pat0, inputs0 =
    abs_cont_bind_outputs span ctx abs0.regions.owned bound cont0
  in
  let bindings0 = !bound.all_bindings in
  let input_bindings0 = !bound.all_input_bindings in
  [%ltrace
    "- pat0: " ^ tepat_to_string ctx pat0 ^ "\n- inputs0: "
    ^ tevalue_to_string ctx inputs0
    ^ "\n- bound_inputs_outputs:\n"
    ^ bound_inputs_outputs_to_string ctx !bound];

  (* Create the outputs for the composed continuation, and its corresponding inputs.

     We simply list all the bound outputs which were not consumed (the free variables
     give us the inputs, and the borrow themselves give us the outputs) by following
     the order in which they were added to the map.
  *)
  let output, output_input_expr =
    merge_abs_conts_generate_output span ctx
      (List.rev (bindings1 @ bindings0))
      !bound
  in

  (* Create the input expression and pattern *)
  let input_pat, input_input =
    merge_abs_conts_generate_input span ctx
      (List.rev (input_bindings1 @ input_bindings0))
      !bound
  in

  (* Create the let-bindings (this is the input expression) *)
  let input = mk_let span abs0.regions.owned pat0 inputs0 output_input_expr in
  let input = mk_let span abs1.regions.owned pat1 inputs1 input in
  let all_regions = RegionId.Set.union abs0.regions.owned abs1.regions.owned in
  let input = mk_let span all_regions input_pat input_input input in

  (* Sanity check: no free variables in the expressions *)
  [%sanity_check] span (not (tevalue_has_fvars input));
  [%sanity_check] span (not (tevalue_has_fvars output));

  (* The continuation itself *)
  let abs_cont = { output = Some output; input = Some input } in

  [%ltrace
    "After merging:" ^ "\n\n- abs0:\n"
    ^ abs_to_string span ctx abs0
    ^ "\n\n- abs1:\n"
    ^ abs_to_string span ctx abs1
    ^ "\n\n- abs_cont:\n"
    ^ abs_cont_to_string span ctx ~indent:"  " abs_cont];

  abs_cont

(** Merge the continuation expressions of two different abstractions. *)
let merge_abs_conts (span : Meta.span) (ctx : eval_ctx) ~(with_abs_conts : bool)
    (abs0 : abs) (abs1 : abs) : abs_cont option =
  match (abs0.cont, abs1.cont) with
  | None, None | None, Some _ | Some _, None -> None
  | Some cont0, Some cont1 ->
      if with_abs_conts then
        Some (merge_abs_conts_aux span ctx abs0 abs1 cont0 cont1)
      else None

(** Auxiliary function.

    Merge two abstractions into one, without updating the context. *)
let merge_abstractions (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) (merge_funs : merge_duplicates_funcs option)
    ~(with_abs_conts : bool) (ctx : eval_ctx) (abs0 : abs) (abs1 : abs) : abs =
  let original_abs0 = abs0 and original_abs1 = abs1 in
  [%ltrace
    "- abs0:\n"
    ^ abs_to_string span ctx abs0
    ^ "\n\n- abs1:\n"
    ^ abs_to_string span ctx abs1];
  (* Sanity check: we can't merge an abstraction with itself *)
  [%sanity_check] span (abs0.abs_id <> abs1.abs_id);

  let abs0 =
    destructure_abs span abs0.kind ~can_end:abs0.can_end
      ~destructure_shared_values:true ctx abs0
  in
  let abs1 =
    destructure_abs span abs1.kind ~can_end:abs1.can_end
      ~destructure_shared_values:true ctx abs1
  in

  (* Compute the ancestor regions, owned regions, etc.
     Note that one of the two abstractions might a parent of the other *)
  let parents =
    AbsId.Set.diff
      (AbsId.Set.union abs0.parents abs1.parents)
      (AbsId.Set.of_list [ abs0.abs_id; abs1.abs_id ])
  in
  let regions =
    let owned = RegionId.Set.union abs0.regions.owned abs1.regions.owned in
    { owned }
  in

  (* Simplify the duplicated shared borrows - TODO: is this really necessary? *)
  let abs0 = abs_simplify_duplicated_borrows span ctx abs0 in
  let abs1 = abs_simplify_duplicated_borrows span ctx abs1 in

  [%ldebug
    "After simplifying the duplicated shared borrows:\n- abs0:\n"
    ^ abs_to_string span ctx abs0
    ^ "\n\n- abs1:\n"
    ^ abs_to_string span ctx abs1];

  (* Phase 1: split the markers (note that the presence of markers is controlled
     by [merge_funs]: if it is [Some] then there can be markers, otherwise there
     can't be).

     We do so because it makes it easier to implement the merge, in cases like this:
     {[
       abs0 { ML l0 } |><| abs1 { |MB l0|, MB l1 }
     ]}

     If we split before merging we get:
     {[
       abs0 { |ML l0|, ︙ML l0︙ } |><| abs1 { |MB l0|, |MB l1|, ︙MB l1︙ }
           ~~> merge
       abs2 { ︙ML l0︙, |MB l1|, ︙MB l1︙ }
           ~~> simplify the complementary markers
       abs2 { ︙ML l0︙, MB l1 }
     ]}
  *)
  let allow_markers = Option.is_some merge_funs in
  let abs0, abs1 =
    if allow_markers then
      (abs_split_markers span ctx abs0, abs_split_markers span ctx abs1)
    else (abs0, abs1)
  in
  if allow_markers then
    [%ldebug
      "After splitting the markers:\n- abs0:\n"
      ^ abs_to_string span ctx abs0
      ^ "\n\n- abs1:\n"
      ^ abs_to_string span ctx abs1]
  else [%ldebug "Did not split the markers"];

  (* Phase 2: simplify the loans coming from the left abstraction with
     the borrows coming from the right abstraction. *)
  let avalues =
    merge_abstractions_merge_loan_borrow_pairs span ~allow_markers ctx abs0 abs1
  in
  [%ldebug
    "avalues after merging the loans from the left with the borrows from the \
     right:\n"
    ^ String.concat "\n" (List.map (tavalue_to_string ctx) avalues)];

  (* Phase 3: we now remove markers, by merging pairs of the same element with
     different markers into one element. To do so, we linearly traverse the list
     of avalues created through the first phase. *)
  let avalues =
    match merge_funs with
    | None -> avalues
    | Some merge_funs ->
        merge_abstractions_merge_markers
          ~original_owners:[original_abs0;original_abs1]
          span merge_funs ctx regions.owned avalues
  in
  [%ldebug
    "avalues after removing markers:\n"
    ^ String.concat "\n" (List.map (tavalue_to_string ctx) avalues)];

  (* Merge the expressions used for the pure translation. *)
  let cont = merge_abs_conts span ctx ~with_abs_conts abs0 abs1 in

  (* *)
  [%cassert] span (AbsLevelSet.is_empty abs0.ended_subabs) "Unimplemented";
  [%cassert] span (AbsLevelSet.is_empty abs1.ended_subabs) "Unimplemented";
  let ended_subabs = AbsLevelSet.empty in

  (* Create the new abstraction *)
  let abs_id = ctx.fresh_abs_id () in
  let abs =
    {
      abs_id;
      kind = abs_kind;
      can_end;
      parents;
      ended_subabs;
      regions;
      avalues;
      cont;
    }
  in

  [%ltrace "resulting abs:\n" ^ abs_to_string span ctx abs];

  (* Keep the original inputs visible if repeated destructuring changes the
     result. The diagnostic is evaluated only on failure and edits no owner. *)
  [%classert] span (abs_is_destructured span true ctx abs)
    (lazy (let repeated = destructure_abs span abs.kind ~can_end:abs.can_end
             ~destructure_shared_values:true ctx abs in
      "Legacy merge result is not stable under destructuring\nsource left:\n"
      ^ abs_to_string span ~with_ended:true ctx original_abs0
      ^ "\nsource right:\n" ^ abs_to_string span ~with_ended:true ctx original_abs1
      ^ "\nresult:\n" ^ abs_to_string span ~with_ended:true ctx abs
      ^ "\nrepeated destructuring:\n" ^ abs_to_string span ~with_ended:true ctx repeated
      ^ "\nexact result: " ^ Values.show_abs abs
      ^ "\nexact repeated result: " ^ Values.show_abs repeated));
  (* Return *)
  abs

(** Merge the regions in a context to a single region *)
let ctx_merge_regions (ctx : eval_ctx) (rid : RegionId.id)
    (rids : RegionId.Set.t) : eval_ctx =
  let rsubst x = if RegionId.Set.mem x rids then rid else x in
  let env = Substitute.env_subst_rids rsubst ctx.env in
  { ctx with env }

(** End the shared loans in a given abstraction which do not have corresponding
    shared borrows in the context *)
let end_endable_shared_loans_at_abs (span : Meta.span) (ctx : eval_ctx)
    (abs_id : AbsId.id) : eval_ctx =
  (* Compute the set of shared borrows appearing in the context *)
  let bids = (fst (compute_ctx_ids ctx)).borrow_ids in

  (* Update the shared borrows in the region abstraction - we assume the
     region abstraction has been destructured
  *)
  let abs = ctx_lookup_abs ctx abs_id in
  let keep_value (av : tavalue) : bool =
    match av.value with
    | ALoan (ASharedLoan (_, bid, _, child)) ->
        [%sanity_check] span (is_aignored child.value);
        BorrowId.Set.mem bid bids
    | _ -> true
  in

  let avalues = List.filter keep_value abs.avalues in
  let abs = { abs with avalues } in
  fst (ctx_subst_abs span ctx abs_id abs)

let merge_into_first_abstraction_legacy (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx)
    (abs_id0 : AbsId.id) (abs_id1 : AbsId.id) : eval_ctx * AbsId.id =
  (* Lookup the abstractions *)
  let abs0 = ctx_lookup_abs ctx abs_id0 in
  let abs1 = ctx_lookup_abs ctx abs_id1 in

  [%ltrace
    "- abs0:\n"
    ^ abs_to_string span ctx abs0
    ^ "\n\n- abs1:\n"
    ^ abs_to_string span ctx abs1];

  (* Small sanity check *)
  [%sanity_check] span (abs_id0 <> abs_id1);

  (* Merge them *)
  let nabs =
    merge_abstractions span abs_kind ~can_end ~with_abs_conts merge_funs ctx
      abs0 abs1
  in
  Invariants.opt_type_check_abs span ctx nabs;

  (* Native merge_abstractions has already constructed a union of the two
     owned sets and composed the original continuations. Its later global
     quotient is an extra normalization. In the mixed concrete/symbolic
     shared case it can make
     a symbolic projection use a concrete leaf's region, whose lifetime may
     already be ended in another branch joined later. Preserve the native
     union whenever this exact shared interface is present, after checking
     every original A/E mask. The native continuation already records each
     input's original owned scope in its let bindings. Nothing in the context
     is renamed, no projection is widened, and no ended region is revived. *)
  let mask_united value =
    List.exists (fun other ->
      shared_borrow_mask_union_pair span ctx nabs.regions.owned [abs0;abs1] value other
      && List.length (List.filter (fun root -> equal_tavalue value root) nabs.avalues) = 1
      && List.exists (fun root -> root == value || root == other) nabs.avalues)
      (abs0.avalues @ abs1.avalues) in
  let retain_native_regions =
    if Sys.getenv_opt "AENEAS_TRACE_NATIVE_SHARED_UNION" = Some "1" then
      Printf.eprintf "NATIVE_SHARED_UNION_INPUT owner=%s owned=%s ended=%s raw=%s\n%!"
        (AbsId.to_string nabs.abs_id) (RegionId.Set.to_string None nabs.regions.owned)
        (RegionId.Set.to_string None ctx.ended_regions) (show_abs nabs);
    if not (InterpPacketRouting.enabled ())
      || RegionId.Set.cardinal nabs.regions.owned <= 1
    then false else
      let has_symbolic=ref false and has_concrete=ref false in
      let flat_shared (value:tavalue) = match value.value with
        | ASymbolic (_, (AProjLoans {consumed=[];borrows=[];_}
            | AProjBorrows {loans=[];_})) ->
            has_symbolic:=true;
            not (TypesUtils.ty_has_mut_borrow_for_region_in_set
              ctx.type_ctx.type_infos nabs.regions.owned value.ty)
            && RegionId.Set.is_empty (RegionId.Set.inter ctx.ended_regions
              (RegionId.Set.inter nabs.regions.owned (TypesUtils.ty_regions value.ty)))
        | ABorrow (ASharedBorrow _) ->
            has_concrete:=true;
            (match value.ty with
            | TRef(_,referent,RShared) ->
                not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            | _ -> false)
        | ALoan (ASharedLoan(_,_,shared,child)) ->
            has_concrete:=true;
            is_aignored child.value
            && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos shared.ty)
            && not (tvalue_has_loans_or_borrows (Some span) ctx shared)
        | _ -> false in
      if List.for_all flat_shared nabs.avalues && !has_symbolic && !has_concrete then begin
        let module P=InterpPacketInterface in
        let pc=P.context_of_eval ctx in
        (try List.iter (fun owner ->
          (* Only the original two masks explicitly united above may grow.
             The output must contain exactly one of those original nodes;
             every unselected A/E node still gets the ordinary union check. *)
          let retained = {owner with avalues=List.filter (fun value -> not (mask_united value)) owner.avalues} in
          ignore (InterpPacketMerge.check_union_masks pc (P.describe_owner pc retained)
            nabs.regions.owned)) [abs0;abs1]
         with InterpPacketMerge.Unsupported message ->
           InterpPacketRouting.reject span ("native shared union: " ^ message));
        true
      end else false in

  [%cassert] span
    (retain_native_regions || not (List.exists mask_united (abs0.avalues @ abs1.avalues)))
    "Shared borrow mask union requires preserving the native owned-region union";

  (* Update the environment: replace the abstraction 0 with the result of the merge,
     remove the abstraction 1 *)
  let ctx = fst (ctx_subst_abs span ctx abs_id0 nabs) in
  let ctx = fst (ctx_remove_abs span ctx abs_id1) in

  (* Merge all the regions from the abstraction into one (the first - i.e., the
     one with the smallest id). Note that we need to do this in the whole
     environment, as those regions may be referenced as ancestor regions by
     the other abstractions, and may be present in symbolic values, etc. (this
     is not the case if there are no nested borrows, but we anticipate).
  *)
  let ctx =
    let regions = nabs.regions.owned in
    (* Pick the first region id (this is the smallest) *)
    let rid = RegionId.Set.min_elt regions in
    (* If there is only one region, do nothing *)
    if retain_native_regions || RegionId.Set.cardinal regions = 1 then ctx
    else
      let rids = RegionId.Set.remove rid regions in
      ctx_merge_regions ctx rid rids
  in

  (* End the loans in the region abstraction which don't have corresponding borrows anymore *)
  let ctx = end_endable_shared_loans_at_abs span ctx nabs.abs_id in
  if retain_native_regions then begin
    (* A native join temporarily retains both marked copies of a shared-borrow
       ID. Global borrow-ID uniqueness applies after collapse eliminates those
       markers (InterpJoin.join_one), not after each intermediate merge. Keep
       all local mask/type/owner checks above and the original full invariant
       at the completed-collapse boundary; check immediately if already unmarked. *)
    let marked = List.exists (function
      | EAbs owner -> abs_has_markers owner
      | EBinding _ | EFrame -> false) ctx.env in
    if not marked then
      Invariants.check_invariants
        ~shared_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_shared_type_for_typing span ctx)
        ~mut_borrow_type_lookup:(InterpSharedPacketSignature.lookup_retained_mut_borrow_type span ctx)
        span ctx;
    if Sys.getenv_opt "AENEAS_TRACE_NATIVE_SHARED_UNION" = Some "1" then
      Printf.eprintf "NATIVE_SHARED_UNION_RETAINED owner=%s regions=%s ended=%s\n%!"
        (AbsId.to_string nabs.abs_id) (RegionId.Set.to_string None nabs.regions.owned)
        (RegionId.Set.to_string None (RegionId.Set.inter nabs.regions.owned ctx.ended_regions))
  end;

  (* Return *)
  (ctx, nabs.abs_id)

(** A packet merge can expose complementary ordinary borrow roots while
    keeping structured histories intact. Reuse the native duplicate callback
    only for complete equal projections with empty histories or the native
    borrow-free concrete shared pair. Every other root,
    including its marker and nested metadata, remains the original object.
    Equality of the full normalized masks under the already checked region
    union makes the callback's choice of either original type immaterial; no
    region coalescing or marker splitting is performed. *)
let merge_packet_borrow_markers span ctx merge_funs owned avalues =
  let module R = InterpPacketRouting in
  let complementary left right =
    (left=PLeft && right=PRight) || (left=PRight && right=PLeft) in
  let try_merge (value : tavalue) (previous : tavalue) =
    match value.value,previous.value with
    | ABorrow (ASharedBorrow (pm,bid,sid)),
      ABorrow (ASharedBorrow (other_pm,other_bid,other_sid))
      when bid=other_bid && complementary pm other_pm ->
        let shared_type ty=match ty with
          | TRef (_,referent,RShared) ->
              not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
          | _ -> false in
        let normalized=normalize_proj_ty owned value.ty in
        R.require span (shared_type value.ty && shared_type previous.ty
          && equal_ty normalized (normalize_proj_ty owned previous.ty))
          "marked duplicate concrete shared borrows have different complete masks";
        let merged=merge_funs.merge_ashared_borrows bid value.ty pm sid
          previous.ty other_pm other_sid in
        R.require span (match merged.value with
          | ABorrow (ASharedBorrow (PNone,result_bid,result_sid)) ->
              result_bid=bid && result_sid<>sid && result_sid<>other_sid
              && equal_ty normalized (normalize_proj_ty owned merged.ty)
          | _ -> false)
          "native concrete shared duplicate callback changed its permission";
        Some merged
    | ASymbolic (pm,AProjBorrows proj),ASymbolic (other_pm,AProjBorrows other)
      when proj.proj.sv_id=other.proj.sv_id && complementary pm other_pm ->
        R.require span (proj.loans=[] && other.loans=[])
          "marked duplicate packet borrows require empty histories";
        let normalized=normalize_proj_ty owned proj.proj.proj_ty in
        R.require span (equal_ty normalized (normalize_proj_ty owned other.proj.proj_ty))
          "marked duplicate packet borrows have different full projection masks";
        R.require span (equal_ty value.ty proj.proj.proj_ty
          && equal_ty previous.ty other.proj.proj_ty)
          "marked duplicate packet borrow wrapper differs from its original type";
        let merged = merge_funs.merge_aborrow_projs value.ty pm proj
          previous.ty other_pm other in
        R.require span (match merged.value with
          | ASymbolic (PNone,AProjBorrows result) ->
              result.loans=[] && result.proj.sv_id=proj.proj.sv_id
              && equal_ty merged.ty result.proj.proj_ty
              && equal_ty normalized (normalize_proj_ty owned result.proj.proj_ty)
          | _ -> false)
          "native duplicate borrow merge changed its complete projection";
        Some merged
    | _ -> None in
  List.fold_left (fun previous value ->
    let rec insert = function
      | [] -> [value]
      | head::tail -> (match try_merge value head with
          | Some merged -> merged::tail
          | None -> head::insert tail) in
    insert previous) [] avalues

(** All public merge routes share this dispatch. A packet rejection must never
    fall through to destructuring/coalescing. The fixed set is required from the
    actual caller; legacy direct/recorded callers that omit it remain explicitly
    unsupported for packets, rather than guessing a frozen set. *)
let merge_into_first_abstraction ?packet_fixed_abs_ids ?packet_replay (span : Meta.span)
    (abs_kind : abs_kind) ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx)
    (abs_id0 : AbsId.id) (abs_id1 : AbsId.id) : eval_ctx * AbsId.id =
  let left = ctx_lookup_abs ctx abs_id0 and right = ctx_lookup_abs ctx abs_id1 in
  let packet_dispatch = InterpPacketRouting.enabled ()
     && (Option.is_some packet_replay || InterpPacketRouting.requires_merge left || InterpPacketRouting.requires_merge right) in
  InterpPacketRouting.trace_route left right packet_dispatch;
  if packet_dispatch then begin
    let module R = InterpPacketRouting in
    let module P = InterpPacketInterface in
    let fixed_aids = match packet_fixed_abs_ids with
      | Some x -> x
      | None -> R.reject span "packet direct/recorded merge lacks original fixed-owner set"
    in
    let allow_marked = Option.is_some merge_funs in
    Option.iter (fun action ->
      R.require span (not allow_marked && with_abs_conts)
        "recorded packet replay requires unmarked synthesis";
      R.validate_merge_replay span ctx action left right) packet_replay;
    R.require span can_end "packet result must remain endable";
    R.require span (Sys.getenv_opt "AENEAS_EXPERIMENTAL_ALL_FRAME_PARENTS" = Some "1")
      "packet commit requires the reviewed all-frame parent-update path";
    List.iter (fun (a : abs) -> match a.kind with
      | SynthInput _ | SynthRet _ -> R.reject span "cannot merge a synthetic boundary owner"
      | _ -> ()) [left;right];
    let targets = AbsId.Set.of_list [abs_id0;abs_id1] in
    env_iter_abs (fun a ->
      if AbsId.Set.mem a.abs_id fixed_aids then
        R.require span (AbsId.Set.is_empty (AbsId.Set.inter a.parents targets))
          "packet commit would rewrite a fixed owner's parent set") ctx.env;
    let ld = R.validate_owner ~allow_marked span ctx left
    and bd = R.validate_owner ~allow_marked span ctx right in
    let duplicate_interface=if allow_marked && Option.is_none packet_replay then
      R.shared_duplicate_interface ~allow_residual_loans:(not with_abs_conts)
        span ctx left right else None in
    let edited_left, edited_right, owned, parents, trace_prefix, trace_detail =
      match packet_replay, R.shared_edge ~allow_marked
        ~allow_symbolic_pair:(not allow_marked && Option.is_none packet_replay) span ld bd with
      | Some ((R.VanishedLeftShared _ | R.VanishedLeftInterface _) as action), _ ->
          (* The recorded edge was on the discarded side. No current edge is
             consumed here: concatenate the exact original projected trees and
             compose their actual continuations, as projection of that merge. *)
          List.iter (fun (owner:abs) ->
            R.require span (owner.can_end
              && (match action with R.VanishedLeftShared _ -> Option.is_some owner.cont | _ -> true)
              && AbsLevelSet.is_empty owner.ended_subabs
              && not (AbsId.Set.mem owner.abs_id fixed_aids))
              "vanished-left composition has a fixed or incomplete owner") [left;right];
          R.require span (left.abs_id<>right.abs_id)
            "vanished-left composition needs distinct original owners";
          let owned=RegionId.Set.union left.regions.owned right.regions.owned in
          let pc=P.context_of_eval ctx in
          let checks=try InterpPacketMerge.check_union_masks pc ld owned
              + InterpPacketMerge.check_union_masks pc bd owned
            with InterpPacketMerge.Unsupported reason -> R.reject span reason in
          let parents=AbsId.Set.diff (AbsId.Set.union left.parents right.parents) targets in
          left,right,owned,parents,"PROJECTED_PACKET_COMPOSITION_COMMITTED",
            " " ^ R.recorded_description action
              ^ " mask_checks=" ^ string_of_int checks
      | _, Some (loan, borrow, bid, sid) ->
          (* This is the native concrete shared-edge rule: remove only the
             matching right borrow, retain the left loan and every symbolic
             permission/history, and compose the ORIGINAL continuations. *)
          List.iter (fun (owner : abs) ->
            R.require span (owner.can_end && not (AbsId.Set.mem owner.abs_id fixed_aids))
              "concrete shared merge has a fixed or non-endable owner";
            R.require span (AbsLevelSet.is_empty owner.ended_subabs)
              "concrete shared merge has ended sublevels";
            if with_abs_conts then
              R.require span (Option.is_some owner.cont)
                "concrete shared synthesis merge is missing a continuation") [left; right];
          R.require span (left.abs_id<>right.abs_id)
            "concrete shared root merge needs distinct owners";
          (* As in marked ordinary packet cancellation, two joined branches
             can retain the same native region. Owned sets are projection
             masks, not permission IDs. The exact same-marker root edge is
             already selected; check_union_masks below still checks every
             retained A/E node before the native union can be committed. *)
          R.require span (allow_marked
            || (match packet_replay with Some (R.RightShared _) -> true | _ -> false)
            || RegionId.Set.is_empty
              (RegionId.Set.inter left.regions.owned right.regions.owned))
            "unmarked concrete shared merge has overlapping owned regions";
          (match loan.value with
          | ALoan (ASharedLoan (marker, actual_bid, shared, _)) ->
              R.require span (actual_bid=bid)
                "concrete shared merge selected a different loan ID";
              if allow_marked then begin
                R.require span (marker<>PNone)
                  "concrete shared collapse requires an explicit same-marker edge";
                (* Observe the unique current loan through the same bounded
                   marker-aware reader used by transient invariants. Native
                   lookup cannot traverse other marked leaves during a join.
                   The actual A root and its payload stay unchanged. *)
                let actual=InterpSharedPacketSignature.lookup_retained_shared_value
                    span ctx marker bid in
                R.require span (actual==shared)
                  "marked concrete shared merge selected another current loan payload"
              end else
                (match ctx_lookup_loan span ek_all bid ctx with
                | AbsId aid, Abstract (ASharedLoan (PNone, actual_bid, _, _)) ->
                    R.require span (aid = left.abs_id && actual_bid = bid)
                      "concrete shared merge selected the wrong native loan owner"
                | _ -> R.reject span "concrete shared merge has no native shared loan")
          | _ -> R.reject span "concrete shared merge selected a non-shared loan");
          (* Native ordinary reduction can expose both a concrete shared edge
             and an independent ordinary symbolic pair between these owners.
             Prepare the symbolic cancellation against the complete ORIGINAL
             environment, then remove precisely the original concrete borrow.
             The original concrete loan and all other typed nodes remain. *)
          let symbolic_pairs=List.concat_map (fun (loan:P.packet) ->
            if loan.polarity<>P.Loan then [] else
            List.filter_map (fun (borrow:P.packet) ->
              if borrow.polarity=P.Borrow && loan.marker=borrow.marker
                && loan.sid=borrow.sid && equal_ty loan.typ.normalized borrow.typ.normalized
              then Some(loan,borrow) else None) (R.roots bd)) (R.roots ld) in
          let edited_left,borrow_owner,symbolic_detail=match symbolic_pairs with
            | [] -> left,right,""
            | [symbolic_loan,symbolic_borrow] ->
                R.require span (not allow_marked && Option.is_none packet_replay
                  && symbolic_loan.marker=PNone && symbolic_borrow.marker=PNone
                  && not symbolic_loan.typ.owned_mutable && not symbolic_borrow.typ.owned_mutable)
                  "mixed shared merge requires one unmarked ordinary shared packet";
                (match P.original_ap symbolic_loan,P.original_ap symbolic_borrow with
                | AProjLoans {consumed=[];borrows=[];_},AProjBorrows {loans=[];_} -> ()
                | _ -> R.reject span "mixed shared merge selected symbolic history");
                let prepared=try InterpPacketMerge.prepare ~with_abs_conts span
                    ~native_type_ctx:ctx.type_ctx (P.context_of_eval ctx)
                    ~current_env:ctx.env ~supplied_env:ctx.env ~fixed_aids
                    ~loan_owner:left ~loan_path:symbolic_loan.at.path
                    ~borrow_owner:right ~borrow_path:symbolic_borrow.at.path
                  with InterpPacketMerge.Unsupported message -> R.reject span message in
                prepared.loan_owner,prepared.borrow_owner,
                  " symbolic_sid=" ^ SymbolicValueId.to_string(Option.get symbolic_loan.sid)
            | _ -> R.reject span "mixed shared merge has multiple symbolic pairs" in
          let avalues = List.filter (fun value -> value != borrow) borrow_owner.avalues in
          R.require span (List.length avalues + 1 = List.length borrow_owner.avalues)
            "concrete shared merge did not remove exactly one borrow root";
          let edited_right = { borrow_owner with avalues } in
          let owned = RegionId.Set.union left.regions.owned right.regions.owned in
          let pc = P.context_of_eval ctx in
          let rd = P.describe_owner pc edited_right in
          let mask_checks =
            try InterpPacketMerge.check_union_masks pc (P.describe_owner pc edited_left) owned
              + InterpPacketMerge.check_union_masks pc rd owned
            with InterpPacketMerge.Unsupported reason -> R.reject span reason in
          let parents = AbsId.Set.diff (AbsId.Set.union left.parents right.parents) targets in
          let detail = " shared_loan=" ^ BorrowId.to_string bid
            ^ " shared_borrow=" ^ SharedBorrowId.to_string sid
            ^ " mask_checks=" ^ string_of_int mask_checks
            ^ " overlapping_regions=" ^ RegionId.Set.to_string None
                (RegionId.Set.inter left.regions.owned right.regions.owned) in
          edited_left, edited_right, owned, parents, "PACKET_SHARED_MERGE_COMMITTED", detail ^ symbolic_detail
      | _, None when Option.is_some duplicate_interface ->
          let left_history,right_history,left_live,right_live,flat,same_key,marker=
            Option.get duplicate_interface in
          R.require span (left.abs_id<>right.abs_id)
            "shared duplicate branch merge needs distinct original owners";
          List.iter (fun (owner:abs) ->
            R.require span (owner.can_end && not(AbsId.Set.mem owner.abs_id fixed_aids)
              && AbsLevelSet.is_empty owner.ended_subabs)
              "shared duplicate branch merge has a fixed or ended owner") [left;right];
          (* Follow merge_abs_conts exactly: a branch analysis can have an
             explicit join continuation on only one side. The native helper
             returns None when either input is absent, and composes both
             original scoped expressions only when both are present. *)
          let owned=RegionId.Set.union left.regions.owned right.regions.owned in
          let pc=P.context_of_eval ctx in
          let checks=try InterpPacketMerge.check_union_masks pc ld owned
              + InterpPacketMerge.check_union_masks pc bd owned
            with InterpPacketMerge.Unsupported message -> R.reject span message in
          let paired=List.filter (fun original -> List.exists (same_key original) right_live) left_live in
          let retained=List.filter (fun original -> not(List.exists (same_key original) right_live)) left_live
            @ List.filter (fun original -> not(List.exists (same_key original) left_live)) right_live in
          R.require span (retained=[] || not with_abs_conts)
            "partial shared duplicate interface is analysis-only";
          let merged=merge_abstractions_merge_markers span (Option.get merge_funs)
              ctx owned (left_live@right_live) in
          let preserved = if retained=[] then
              List.length merged=List.length left_live
              && List.for_all2 (fun original value -> flat value && same_key original value
                && marker value=Some PNone) left_live merged
            else List.length merged=List.length paired+List.length retained
              && List.for_all (fun original ->
                match List.filter (same_key original) merged with
                | [value] -> flat value && marker value=Some PNone
                    && equal_ty original.ty value.ty
                | _ -> false) paired
              && List.for_all (fun original ->
                List.length(List.filter (fun value -> value==original) merged)=1) retained in
          R.require span preserved
            "native duplicate callback changed a shared input or retained output";
          let edited_left={left with avalues=merged@left_history@right_history}
          and edited_right={right with avalues=[]} in
          let parents=AbsId.Set.diff (AbsId.Set.union left.parents right.parents) targets in
          edited_left,edited_right,owned,parents,"PACKET_DUPLICATE_MERGE_COMMITTED",
            " roots=" ^ string_of_int(List.length merged)
              ^ " mask_checks=" ^ string_of_int checks
      | _, None ->
          let pairs =
            try R.complementary_pairs ~allow_marked span ld bd with error ->
              let backtrace=Printexc.get_raw_backtrace () in
              Printf.eprintf "PACKET_PAIR_SELECTION_REJECTED marked=%b synthesis=%b\nleft:\n%s\nright:\n%s\n%!"
                allow_marked with_abs_conts
                (abs_to_string span ~with_ended:true ctx left)
                (abs_to_string span ~with_ended:true ctx right);
              Printexc.raise_with_backtrace error backtrace in
          (* Each independent edge is prepared against the original complete
             context, never against a fabricated intermediate environment. *)
          let prepared = List.map (fun ((loan:P.packet),(borrow:P.packet)) ->
            R.require span (not allow_marked || loan.marker<>PNone)
              "packet collapse requires an explicit same-marker cancellation edge";
            try InterpPacketMerge.prepare ~with_abs_conts ~allow_marked span ~native_type_ctx:ctx.type_ctx
              (P.context_of_eval ctx) ~current_env:ctx.env ~supplied_env:ctx.env
              ~fixed_aids ~loan_owner:left ~loan_path:loan.at.path
              ~borrow_owner:right ~borrow_path:borrow.at.path
            with InterpPacketMerge.Unsupported reason ->
              R.reject span (reason ^ "\nselected loan: " ^ String.concat "/" loan.at.path
                ^ "\n" ^ abs_to_string span ~with_ended:true ctx left
                ^ "\nselected borrow: " ^ String.concat "/" borrow.at.path
                ^ "\n" ^ abs_to_string span ~with_ended:true ctx right)) pairs in
          let first=List.hd prepared in
          let pc=P.context_of_eval ctx in
          let edited_left,edited_right,final_mask_checks = match prepared with
            | [one] -> one.loan_owner,one.borrow_owner,0
            | _ ->
                (* Distinct history-free SIDs ensure disjoint selected paths.
                   Each replacement requires the original node/marker identity
                   and verifies preservation relative to the preceding tree;
                   every unrelated wrapper, level and metadata object survives. *)
                let edit owner selected = List.fold_left (fun owner (packet:P.packet) ->
                  let before=P.describe_owner pc owner in
                  let changed=InterpPacketMerge.replace_root owner packet in
                  InterpPacketMerge.check_conservation before
                    (P.describe_owner pc changed) packet.at.path;
                  changed) owner selected in
                (try
                  let l=edit left (List.map fst pairs)
                  and r=edit right (List.map snd pairs) in
                  let checks=InterpPacketMerge.check_union_masks pc (P.describe_owner pc l) first.owned
                    + InterpPacketMerge.check_union_masks pc (P.describe_owner pc r) first.owned in
                  l,r,checks
                with InterpPacketMerge.Unsupported reason -> R.reject span reason) in
          let sum f = List.fold_left (fun total p -> total+f p) 0 prepared in
          let detail = " roots=" ^ String.concat ";" (List.map (fun ((loan:P.packet),(borrow:P.packet)) ->
                String.concat "/" loan.at.path ^ " / " ^ String.concat "/" borrow.at.path) pairs)
            ^ " mask_checks=" ^ string_of_int (final_mask_checks + sum (fun p->p.regular_mask_checks))
            ^ " child_e_checks=" ^ string_of_int (sum (fun p->p.child_e_checks))
            ^ " removed_nodes=" ^ string_of_int (sum (fun p->
                List.length p.removed_loan_nodes + List.length p.removed_borrow_nodes))
            ^ " ignored_root_metadata=" ^ string_of_int (sum (fun p->List.length p.ignored_root_metadata)) in
          edited_left,edited_right,first.owned,first.parents,"PACKET_MERGE_COMMITTED",detail
    in
    R.check_parent_commit span ctx left right parents;
    (* Exactly the existing analysis/synthesis split: analysis creates no E
       continuation, synthesis composes the two ORIGINAL owners through the real
       helper, preserving its calls, bindings, effects and failures. *)
    let cont = merge_abs_conts span ctx ~with_abs_conts left right in
    let avalues = edited_left.avalues @ edited_right.avalues in
    let avalues = match merge_funs with
      | None -> avalues
      | Some merge_funs -> merge_packet_borrow_markers span ctx merge_funs owned avalues in
    let nabs = {
      abs_id = ctx.fresh_abs_id (); kind = abs_kind; can_end;
      parents; ended_subabs = AbsLevelSet.empty;
      regions = { owned }; avalues; cont;
    } in
    ignore (R.validate_owner ~allow_marked span ctx nabs);
    Invariants.opt_type_check_abs span ctx nabs;
    (* The standard substitution/removal updates current-frame parent edges.
       No region coalescing, history flattening or implicit loan ending occurs. *)
    let nctx = fst (ctx_subst_abs span ctx abs_id0 nabs) in
    let nctx = R.remap_borrower_parents abs_id1 nabs.abs_id nctx in
    let nctx = fst (ctx_remove_abs span nctx abs_id1) in
    (* As in the native merger, intermediate join contexts may retain both
       marked copies of one shared-borrow ID. The closure, conservation, union
       masks and complete local typing checks above apply now; global uniqueness
       is checked at the original completed-collapse boundary. Never interpret
       a pair of branch copies as a single available runtime permission. *)
    let marked=List.exists (function
      | EAbs owner -> abs_has_markers owner
      | EBinding _ | EFrame -> false) nctx.env in
    if not marked then Invariants.check_invariants span nctx;
    if Sys.getenv_opt "AENEAS_TRACE_PACKET_MERGE" = Some "1" then
      prerr_endline (trace_prefix ^ " loan=" ^ AbsId.to_string abs_id0
        ^ " borrow=" ^ AbsId.to_string abs_id1 ^ " result=" ^ AbsId.to_string nabs.abs_id
        ^ " with_abs_conts=" ^ string_of_bool with_abs_conts ^ trace_detail);
    (nctx,nabs.abs_id)
  end else
    merge_into_first_abstraction_legacy span abs_kind ~can_end ~with_abs_conts
      merge_funs ctx abs_id0 abs_id1

(** Reorder the loans and borrows inside the fresh abstractions.

    See {!reorder_fresh_abs}.

    TODO: having to do this is a bit annoying. We should rather generalize the
    match/join operations to not be dependent on the order of the borrows/loans.
*)
let reorder_loans_borrows_in_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let type_infos = ctx.type_ctx.type_infos in
  let reorder_in_fresh_abs (abs : abs) : abs =
    [%ltrace "abs:\n" ^ abs_to_string span ctx abs];
    (* Filter the avalues *)
    let filter (v : tavalue) : bool =
      match v.value with
      | AAdt _ | ASymbolic _ -> true
      | ALoan lc -> (
          match lc with
          | AMutLoan _ | ASharedLoan _ -> true
          | AEndedMutLoan { child; given_back; given_back_meta = _ } ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              [%cassert] span (is_aignored given_back.value) "Not supported yet";
              false
          | AEndedSharedLoan (sv, child) ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              [%cassert] span
                (not
                   (ValuesUtils.value_has_loans_or_borrows (Some span)
                      type_infos sv.value))
                "Not implemented yet";
              false
          | AIgnoredMutLoan (_, child) ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              false
          | AEndedIgnoredMutLoan { child; given_back; given_back_meta = _ } ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              [%cassert] span (is_aignored given_back.value) "Not supported yet";
              false
          | AIgnoredSharedLoan child ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              false)
      | ABorrow bc -> (
          match bc with
          | AMutBorrow _ | ASharedBorrow _ -> true
          | AIgnoredMutBorrow (_, child) ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              false
          | AEndedMutBorrow (_, child) ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              false
          | AEndedSharedBorrow -> false
          | AEndedIgnoredMutBorrow { child; given_back; given_back_meta = _ } ->
              [%cassert] span (is_aignored child.value) "Not supported yet";
              [%cassert] span (is_aignored given_back.value) "Not supported yet";
              false
          | AProjSharedBorrow _ -> [%craise] span "Not supported yet")
      | AIgnored _ -> false
    in
    let avalues = List.filter filter abs.avalues in

    (* Split between the loans and borrows, and between the concrete
       and symbolic values. *)
    let is_borrow (av : tavalue) : bool =
      match av.value with
      | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
      | ALoan _ | ASymbolic (_, AProjLoans _) -> false
      | _ -> [%craise] span ("Unexpected avalue: " ^ tavalue_to_string ctx av)
    in
    let is_concrete (av : tavalue) : bool =
      match av.value with
      | ABorrow _ | ALoan _ -> true
      | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> false
      | _ -> [%craise] span ("Unexpected avalue: " ^ tavalue_to_string ctx av)
    in
    let aborrows, aloans = List.partition is_borrow avalues in
    let aborrows, borrow_projs = List.partition is_concrete aborrows in
    let aloans, loan_projs = List.partition is_concrete aloans in

    (* Reoder the borrows, and the loans.

       After experimenting, it seems that a good way of reordering the loans
       and the borrows to find fixed points is simply to sort them by increasing
       order of id (taking the smallest id of a set of ids, in case of sets).

       This is actually not as arbitrary as it might seem, because the ids give
       us the order in which we introduced those borrows/loans.

       We do the same thing for the symbolic values: we use the symbolic ids.
       The final order is:
         borrows, borrow projectors, loans, loan projectors
       (all sorted by increasing id)
    *)
    let get_borrow_id (av : tavalue) : BorrowId.id =
      match av.value with
      | ABorrow (AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          bid
      | _ -> [%craise] span ("Unexpected value: " ^ tavalue_to_string ctx av)
    in
    let get_loan_id (av : tavalue) : BorrowId.id =
      match av.value with
      | ALoan (AMutLoan (pm, lid, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          lid
      | ALoan (ASharedLoan (pm, lid, _, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          lid
      | _ -> [%craise] span ("Unexpected value: " ^ tavalue_to_string ctx av)
    in
    let get_symbolic_id (av : tavalue) : SymbolicValueId.id =
      match av.value with
      | ASymbolic (pm, aproj) -> begin
          [%sanity_check] span (allow_markers || pm = PNone);
          match aproj with
          | AProjLoans { proj; _ } | AProjBorrows { proj; _ } -> proj.sv_id
          | _ -> [%craise] span "Unexpected"
        end
      | _ -> [%craise] span ("Unexpected value: " ^ tavalue_to_string ctx av)
    in
    let compare_pair :
        'a. ('a -> 'a -> int) -> 'a * tavalue -> 'a * tavalue -> int =
     fun compare_id x y ->
      let fst = compare_id (fst x) (fst y) in
      [%cassert] span (fst <> 0)
        ("Unexpected: can't compare: '"
        ^ tavalue_to_string ctx (snd x)
        ^ "' with '"
        ^ tavalue_to_string ctx (snd y)
        ^ "'");
      fst
    in
    (* We use ordered maps to reorder the borrows and loans *)
    let reorder :
        'a. (tavalue -> 'a) -> ('a -> 'a -> int) -> tavalue list -> tavalue list
        =
     fun get_id compare_id values ->
      let values = List.map (fun v -> (get_id v, v)) values in
      List.map snd (List.stable_sort (compare_pair compare_id) values)
    in
    let aborrows = reorder get_borrow_id compare_borrow_id aborrows in
    let borrow_projs =
      reorder get_symbolic_id compare_symbolic_value_id borrow_projs
    in
    let aloans = reorder get_loan_id compare_borrow_id aloans in
    let loan_projs =
      reorder get_symbolic_id compare_symbolic_value_id loan_projs
    in
    let avalues = List.concat [ aborrows; borrow_projs; aloans; loan_projs ] in
    { abs with avalues }
  in

  (* Small helper: returns [true] if a region abstraction was introduced exactly
     because of a function call *)
  let abs_is_fun_call (abs : abs) =
    match abs.cont with
    | Some { output = _; input = Some { value = EApp (EFunCall _, _); _ } } ->
        true
    | _ -> false
  in
  let abs_has_adt (abs : abs) =
    let visitor =
      object
        inherit [_] iter_tavalue
        method! visit_AAdt _ _ = raise Utils.Found
      end
    in
    try
      List.iter (visitor#visit_tavalue ()) abs.avalues;
      false
    with Utils.Found -> true
  in

  let reorder_in_abs (abs : abs) =
    (* We do not update the fixed region abstractions as well as the ones
       which were introduced exactly by function calls (we update those which
       were introduced when promoting anonymous values to region abstractions
       or by merging region abstractions). We also do not reorder the abstractions
       containing ADTs (those should actually have been introduced by function
       calls).

       TODO: remove the need to reorder the values by making the match/join operations
       more general.
     *)
    if
      AbsId.Set.mem abs.abs_id old_abs_ids
      || abs_is_fun_call abs || abs_has_adt abs
    then abs
    else if InterpPacketRouting.enabled () && InterpPacketRouting.has_history abs then (
      (* Keep every ordered wrapper/history/given-back branch. Global owner
         ordering below remains unchanged; no legacy avalue filter is applied. *)
      ignore (InterpPacketRouting.validate_owner ~allow_marked:allow_markers span ctx abs);
      abs)
    else if InterpPacketRouting.enabled () && InterpPacketRouting.has_empty abs then (
      InterpPacketRouting.validate_empty_order ~allow_marked:allow_markers span ctx abs;
      abs)
    else if InterpPacketRouting.enabled () && InterpPacketRouting.needs_packet abs then (
      ignore (InterpPacketRouting.validate_owner ~allow_marked:allow_markers span ctx abs);
      abs)
    else reorder_in_fresh_abs abs
  in

  let env = env_map_abs reorder_in_abs ctx.env in

  { ctx with env }

type tavalue_list = tavalue list [@@deriving ord, show]

module OrderedTypedAvalueList :
  Collections.OrderedType with type t = tavalue list = struct
  type t = tavalue_list

  let compare x y = compare_tavalue_list x y
  let to_string x = show_tavalue_list x
  let pp_t fmt x = Format.pp_print_string fmt (show_tavalue_list x)
  let show_t x = show_tavalue_list x
end

let reorder_fresh_abs_aux (span : Meta.span) (old_abs_ids : AbsId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  (* **WARNING:** remember that the environments store the bindings in *reverse*
     order (the fresh values/abstractions get pushed at the beginning of the list,
     and when printing the environments we reverse them first) *)
  (* Split between the fresh abstractions and the rest of the context *)
  let env, fresh_abs =
    List.partition
      (function
        | EAbs abs -> AbsId.Set.mem abs.abs_id old_abs_ids
        | _ -> true)
      ctx.env
  in

  (* Reorder the fresh abstractions.

     We use the content of the abstractions to reorder them.
     In practice, this allows us to reorder the abstractions by using the ids
     of the loans, borrows and symbolic values. This is far from perfect, but
     allows us to have a quite simple matching algorithm for now, to compute
     the joins as well as to check whether two environments are equivalent.
     We may want to make this algorithm more general in the future.
  *)
  let cmp abs0 abs1 =
    match (abs0, abs1) with
    | EAbs abs0, EAbs abs1 -> compare_tavalue_list abs0.avalues abs1.avalues
    | _ -> [%internal_error] span
  in
  let fresh_abs = List.sort cmp fresh_abs |> List.rev in

  (* Reconstruct the environment *)
  let env = fresh_abs @ env in

  { ctx with env }

let reorder_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  reorder_loans_borrows_in_fresh_abs span allow_markers old_abs_ids ctx
  |> reorder_fresh_abs_aux span old_abs_ids

type proj_ctx = {
  inside_output : bool;  (** Are we inside an abstraction output expression? *)
}

let project_context (span : Meta.span) (fixed_aids : AbsId.Set.t)
    (pm : proj_marker) (ctx : eval_ctx) : eval_ctx =
  [%cassert] span (pm = PLeft || pm = PRight) "Invalid input";
  let project_left = pm = PLeft in

  let preserve (pm' : proj_marker) =
    match (pm, pm') with
    | PLeft, (PNone | PLeft) -> true
    | PRight, (PNone | PRight) -> true
    | _ -> false
  in

  let visitor =
    object (self)
      inherit [_] map_eval_ctx as super

      (* By overriding this method to raise an exception we make sure we do not
         miss any projection marker *)
      method! visit_proj_marker _ _ = [%internal_error] span

      method! visit_ASymbolic env pm aproj =
        if preserve pm then
          let aproj = self#visit_aproj env aproj in
          ASymbolic (PNone, aproj)
        else begin
          match aproj with
          | AProjLoans { proj = _; consumed; borrows } ->
              [%cassert] span (consumed = []) "Not implemented";
              [%cassert] span (borrows = []) "Not implemented";
              AIgnored None
          | AProjBorrows { proj = _; loans } ->
              [%cassert] span (loans = []) "Not implemented";
              AIgnored None
          | AEndedProjLoans { proj_ty = _; proj = _; consumed; borrows } ->
              [%cassert] span (consumed = []) "Not implemented";
              [%cassert] span (borrows = []) "Not implemented";
              AIgnored None
          | AEndedProjBorrows _ ->
              (* We shouldn't find ended borrows inside a region abstraction *)
              [%internal_error] span
          | AEmpty -> AIgnored None
        end

      method! visit_ALoan env lc =
        match lc with
        | AMutLoan (pm, lid, child) ->
            if preserve pm then
              let child = self#visit_tavalue env child in
              ALoan (AMutLoan (PNone, lid, child))
            else (
              [%cassert] span (is_aignored child.value) "Not implemented";
              AIgnored None)
        | ASharedLoan (pm, lid, shared, child) ->
            if preserve pm then
              let child = self#visit_tavalue env child in
              ALoan (ASharedLoan (PNone, lid, shared, child))
            else (
              [%cassert] span (is_aignored child.value) "Not implemented";
              AIgnored None)
        | AEndedMutLoan _
        | AEndedSharedLoan _
        | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _
        | AIgnoredSharedLoan _ ->
            (* Those do not have projection markers *)
            super#visit_ALoan env lc

      method! visit_ABorrow env bc =
        match bc with
        | AMutBorrow (pm, bid, child) ->
            if preserve pm then
              let child = self#visit_tavalue env child in
              ABorrow (AMutBorrow (PNone, bid, child))
            else (
              [%cassert] span (is_aignored child.value) "Not implemented";
              AIgnored None)
        | ASharedBorrow (pm, bid, sid) ->
            if preserve pm then ABorrow (ASharedBorrow (PNone, bid, sid))
            else AIgnored None
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _
        | AProjSharedBorrow _ ->
            (* Those do not have projection markers *)
            super#visit_ABorrow env bc

      method! visit_tevalue env v =
        (* We need to preserve the type when projecting joins (the type
           is not always constent because of loans) - TODO: remove those
           types. *)
        match v.value with
        | EJoinMarkers (left, right) ->
            let v = if project_left then left else right in
            self#visit_tevalue env v
        | _ -> super#visit_tevalue env v

      method! visit_ESymbolic env pm eproj =
        if preserve pm then
          let eproj = self#visit_eproj env eproj in
          ESymbolic (PNone, eproj)
        else
          match eproj with
          | EProjLoans { proj = _; consumed; borrows } ->
              [%cassert] span (consumed = []) "Not implemented";
              [%cassert] span (borrows = []) "Not implemented";
              EBottom
          | EProjBorrows { proj = { sv_id; proj_ty }; loans } ->
              [%cassert] span (loans = []) "Not implemented";
              if env.inside_output then
                EIgnored
                  (Some
                     ( ctx.env,
                       mk_tvalue_from_symbolic_value { sv_id; sv_ty = proj_ty }
                     ))
              else EBottom
          | EEndedProjLoans { proj_ty = _; proj = _; consumed; borrows } ->
              [%cassert] span (consumed = []) "Not implemented";
              [%cassert] span (borrows = []) "Not implemented";
              EBottom
          | EEndedProjBorrows _ ->
              (* We can't find ended borrows in live abstractions *)
              [%internal_error] span
          | EEmpty -> EIgnored None

      method! visit_ELoan env lc =
        match lc with
        | EMutLoan (pm, lid, child) ->
            if preserve pm then
              let child = self#visit_tevalue env child in
              ELoan (EMutLoan (PNone, lid, child))
            else (
              [%cassert] span (is_eignored child.value) "Not implemented";
              EBottom)
        | EEndedMutLoan _ | EIgnoredMutLoan _ | EEndedIgnoredMutLoan _ ->
            (* Those do not have projection markers *)
            super#visit_ELoan env lc

      method! visit_EBorrow env lc =
        match lc with
        | EMutBorrow (pm, bid, child) ->
            if preserve pm then
              let child = self#visit_tevalue env child in
              EBorrow (EMutBorrow (PNone, bid, child))
            else (
              [%cassert] span (is_eignored child.value) "Not implemented";
              if env.inside_output then EIgnored None else EBottom)
        | EIgnoredMutBorrow _ | EEndedMutBorrow _ | EEndedIgnoredMutBorrow _ ->
            (* Those do not have projection markers *)
            super#visit_EBorrow env lc

      method! visit_abs_cont env abs =
        let { output; input } = abs in
        let output =
          Option.map (self#visit_tevalue { inside_output = true }) output
        in
        let input = Option.map (self#visit_tevalue env) input in
        { output; input }
    end
  in
  (* Project *)
  let ctx = visitor#visit_eval_ctx { inside_output = false } ctx in

  (* Simplify the region abstractions, and filter the ones which have become
     empty because of the projection *)
  let update_binding (e : env_elem) : env_elem option =
    match e with
    | EAbs abs ->
        if (not abs.can_end) || AbsId.Set.mem abs.abs_id fixed_aids then Some e
        else
          let keep_value (e : tavalue) : bool = not (is_aignored e.value) in
          let avalues = List.filter keep_value abs.avalues in
          if avalues = [] then None else Some (EAbs { abs with avalues })
    | EBinding _ | EFrame -> Some e
  in
  let env = List.filter_map update_binding ctx.env in
  { ctx with env }

let add_abs_cont_to_abs_legacy span (ctx : eval_ctx) (abs : abs) (abs_fun : abs_fun) :
    abs =
  [%ltrace "- abs:\n" ^ abs_to_string span ctx abs];
  (* We need to destructure the abs, otherwise when translating the abs as a
     continuation it is tricky to compute its type when some loans have been
     ended but not others (in particular, it is tricky if we have an ADT
     containing partially ended loans) *)
  let abs =
    destructure_abs span abs.kind ~can_end:abs.can_end
      ~destructure_shared_values:true ctx abs
  in
  let regions = abs.regions.owned in
  [%ldebug "- abs after destructure:\n" ^ abs_to_string span ctx abs];
  (* Retrieve the *mutable* borrows/loans from the abstraction values *)
  let borrows : tevalue list ref = ref [] in
  let loans : tevalue list ref = ref [] in
  let get_borrow_loan (x : tavalue) : unit =
    let ty = x.ty in
    match x.value with
    | ALoan lc -> (
        match lc with
        | AMutLoan (pm, bid, child) ->
            [%sanity_check] span (is_aignored child.value);
            let value : evalue =
              ELoan (EMutLoan (pm, bid, mk_eignored None child.ty))
            in
            loans := { value; ty } :: !loans
        | ASharedLoan _ ->
            (* We ignore shared loans *)
            ()
        | AEndedMutLoan _
        | AEndedSharedLoan _
        | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _
        | AIgnoredSharedLoan _ -> [%internal_error] span)
    | ABorrow bc -> (
        match bc with
        | AMutBorrow (pm, bid, child) ->
            [%sanity_check] span (is_aignored child.value);
            let value : evalue =
              EBorrow (EMutBorrow (pm, bid, mk_eignored None child.ty))
            in
            borrows := { value; ty } :: !borrows
        | ASharedBorrow _ -> (* We ignore shared borrows *) ()
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _
        | AProjSharedBorrow _ -> [%internal_error] span)
    | ASymbolic (pm, aproj) -> (
        match aproj with
        | AProjLoans { proj = { sv_id; proj_ty }; consumed; borrows } ->
            if
              TypesUtils.ty_has_mut_borrow_for_region_in_set
                ctx.type_ctx.type_infos regions proj_ty
            then (
              [%sanity_check] span (consumed = []);
              [%sanity_check] span (borrows = []);
              let value : evalue =
                ESymbolic
                  ( pm,
                    EProjLoans
                      { proj = { sv_id; proj_ty }; consumed = []; borrows = [] }
                  )
              in
              loans := { value; ty } :: !loans)
        | AProjBorrows { proj = { sv_id; proj_ty }; loans } ->
            if
              TypesUtils.ty_has_mut_borrow_for_region_in_set
                ctx.type_ctx.type_infos regions proj_ty
            then (
              [%sanity_check] span (loans = []);
              let value : evalue =
                ESymbolic
                  (pm, EProjBorrows { proj = { sv_id; proj_ty }; loans = [] })
              in
              borrows := { value; ty } :: !borrows)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            [%internal_error] span)
    | AAdt _ | AIgnored _ -> [%internal_error] span
  in
  List.iter get_borrow_loan abs.avalues;

  (* Transform them into input/output expressions *)
  let output = mk_etuple ~borrow_proj:true (List.rev !borrows) in
  let input = EApp (abs_fun, [ List.rev !loans ]) in
  let input : tevalue = { value = input; ty = output.ty } in

  (* Put everything together *)
  let cont : abs_cont option =
    Some { output = Some output; input = Some input }
  in
  { abs with cont }


(** Multi-exit entry/output and branch constructors opt in for a checked shared-only
    interface. The original A tree is the signature witness; it is not
    destructured or filtered. Check every native sublevel before registering
    the empty mutable ELoop/EJoin interface, retaining all history and metadata. *)
let add_abs_cont_to_abs ?(shared_packet_signature = false) span
    (ctx : eval_ctx) (abs : abs) (abs_fun : abs_fun) : abs =
  if shared_packet_signature && InterpSharedPacketSignature.enabled ()
     && InterpSharedPacketSignature.needs_explicit_signature abs then begin
    (match abs_fun with
    | ELoop (id, _) | EJoin id when id = abs.abs_id -> ()
    | _ -> InterpSharedPacketSignature.reject span
        "shared constructor requires this owner's ELoop or EJoin");
    let signature = InterpSharedPacketSignature.check span ctx abs in
    InterpSharedPacketSignature.require span
      (List.for_all (InterpSharedHistory.empty_native_interface span ctx abs) abs.avalues)
      "loop signature has a mutable interface at an original native sublevel";
    let output = mk_etuple ~borrow_proj:true [] in
    let input : tevalue = {value=EApp(abs_fun,[[]]);ty=output.ty} in
    {signature.owner with cont=Some {output=Some output;input=Some input}}
  end else add_abs_cont_to_abs_legacy span ctx abs abs_fun
