(** A final loop-application view of an entirely shared abstraction interface.
    Owned regions of this exact interface end together (end_abs_aux). Their
    internal names need not be bijective after projecting a previously joined
    context. This does not rename regions or delete historical A/E values;
    ordinary fixed-point equivalence never uses this view. *)
open Types
open Values
open Contexts
module Existing = InterpSharedHistory
module P = InterpPacketInterface

type endpoint = {sid:symbolic_value_id; polarity:P.polarity; full:ty; mask:ty}
type view = {
  fixed_borrows:tavalue list;
  projectors:endpoint list;
  concrete:(tavalue * ty) list;
  history_values:symbolic_value SymbolicValueId.Map.t;
}

(** Follow precisely the native ELet scope: rids' applies to its bound value
    and pattern, while next keeps the outer scope (SymbolicToPureAbs). Restrict
    this route to ignored data, ADTs and preserved calls, with no live mutable
    interface, concrete consumed EValue, mutable-input wrapper, or variable.
    Ignored captures are neither evaluated here nor removed from the context. *)
let continuation_is_shared (ctx:eval_ctx) (owner:abs) =
  let no_mut regions ty = not (TypesUtils.ty_has_mut_borrow_for_region_in_set
    ctx.type_ctx.type_infos regions ty) in
  let rec pattern regions (p:tepat) = no_mut regions p.ty && match p.pat with
    | PIgnored -> true
    | PAdt (_,fields) -> List.for_all (pattern regions) fields
    | POpen _ | PBound -> false in
  let rec value regions (v:tevalue) = match v.value with
    | ELet (bound_regions,pat,bound,next) ->
        pattern bound_regions pat && value bound_regions bound && value regions next
    | EApp (_,args) -> no_mut regions v.ty
        && List.for_all (List.for_all (value regions)) args
    | EAdt adt -> no_mut regions v.ty && List.for_all (value regions) adt.fields
    | EIgnored _ -> no_mut regions v.ty
    | _ -> false in
  match owner.cont with
  | Some {input=Some input;output=Some output} ->
      value owner.regions.owned input && value owner.regions.owned output
  | _ -> false

let view span (ctx:eval_ctx) fixed_regions (owner:abs) : view option =
  let phase=ref "owner shape or continuation" in
  let prefix_regions_seen=ref RegionId.Set.empty in
  (* This optional matching view admits only plain shared referents. A valid
     native borrow may instead refer to data containing concrete loans; leave
     that case to the ordinary matcher rather than invoking the stricter
     retained-leaf checker and aborting candidate selection. *)
  let plain_shared_referent bid =
    let shared=InterpBorrowsCore.lookup_shared_value span ctx.env bid in
    not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared) in
  (* A concrete shared source reborrow can have a fresh, live outer lifetime
     while its referent is held by a frozen input abstraction. Keep that
     anchored prefix under the ordinary exact BID/type matcher; only the
     following existential shared group uses the final interface view. *)
  let frozen_source bid =
    List.exists (function
      | EAbs source when not source.can_end ->
          List.exists (fun (value:tavalue) -> match value.value with
            | ALoan(ASharedLoan(PNone,lid,_,_)) -> lid=bid
            | _ -> false) source.avalues
      | _ -> false) ctx.env in
  let result =
  if not (owner.can_end && AbsId.Set.is_empty owner.parents
    && AbsLevelSet.is_empty owner.ended_subabs
    && continuation_is_shared ctx owner) then None
  else
    let removed,live=List.partition (Existing.permission_free_history span ctx) owner.avalues in
    let ()=phase:="historical native interfaces" in
    if not (List.for_all (Existing.empty_native_interface span ctx owner) removed) then None
    else
      (* These leading shared permissions keep their fixed or ended outer lifetime
         and are matched by the ordinary native avalue matcher. Only the following
         shared group uses the non-bijective final-interface view. A borrow-free
         concrete referent can retain its native ID after that ghost region was
         ended in another branch; use the existing strict reader/type checks. *)
      let rec fixed_prefix (values : tavalue list) = match values with
        | ({value=ABorrow(ASharedBorrow(PNone,bid,_));
            ty=TRef(RVar(Free region),referent,RShared)} as root)::rest
          when RegionId.Set.mem region owner.regions.owned
            && (RegionId.Set.mem region fixed_regions
              || RegionId.Set.mem region ctx.ended_regions || frozen_source bid)
            && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            && plain_shared_referent bid ->
            InterpSharedPacketSignature.check_retained_shared_borrow
              span ctx owner 0 root;
            let roots,regions,rest=fixed_prefix rest in
            root::roots,RegionId.Set.add region regions,rest
        | roots -> [],RegionId.Set.empty,roots in
      (* With exactly one concrete input and one symbolic output, the input
         belongs to the shared interface itself, not the fixed prefix of a
         later projector pair. Its borrow-free outer lifetime may already be
         ended; the native BID and unended sublevel still carry the permission.
         Keep fixed lifetimes outside this existential owner-group view. *)
      let input_ghost_regions = match live with
        | [{value=ABorrow(ASharedBorrow(PNone,bid,_));
            ty=TRef(RVar(Free region),referent,RShared)};
           {value=ASymbolic(PNone,AProjLoans {consumed=[];borrows=[];_});_}]
          when RegionId.Set.mem region owner.regions.owned
            && not (RegionId.Set.mem region fixed_regions)
            && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            && plain_shared_referent bid -> RegionId.Set.singleton region
        | _ -> RegionId.Set.empty in
      let fixed_borrows,prefix_regions,live =
        if RegionId.Set.is_empty input_ghost_regions then fixed_prefix live
        else [],RegionId.Set.empty,live in
      let ()=prefix_regions_seen:=prefix_regions;phase:="non-prefix owned regions overlap fixed or ended" in
      let excluded=RegionId.Set.union fixed_regions ctx.ended_regions in
      if not (RegionId.Set.is_empty (RegionId.Set.inter excluded
        (RegionId.Set.diff owner.regions.owned
          (RegionId.Set.union prefix_regions input_ghost_regions)))) then None
      else
      (* The native loop-input collector still observes concrete symbolic
         payloads in ended shared loans. Retain that exact inventory so final
         matching establishes its ordinary value substitution too. *)
      let _,history_ids=InterpUtils.compute_abs_ids
        {owner with avalues=removed;cont=None} in
      let history_values=history_ids.sids_to_values in
      let endpoint (value:tavalue) =
        let ()=phase:="symbolic endpoint type or region mask" in
        let selected=match value.value with
          | ASymbolic (PNone,AProjBorrows {proj;loans=[]}) -> Some (P.Borrow,proj)
          | ASymbolic (PNone,AProjLoans {proj;consumed=[];borrows=[]}) -> Some (P.Loan,proj)
          | _ -> None in
        Option.bind selected (fun (polarity,proj) ->
          let typ=P.view_type (P.context_of_eval ctx) owner proj.proj_ty in
          let info=TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos proj.proj_ty in
          if equal_ty value.ty proj.proj_ty && not info.contains_mut_borrow
            && not info.contains_static && not (RegionId.Set.is_empty typ.free_regions)
            && RegionId.Set.subset typ.free_regions owner.regions.owned
            && RegionId.Set.is_empty (RegionId.Set.inter typ.free_regions excluded) then
            Some {sid=proj.sv_id;polarity;full=proj.proj_ty;mask=typ.normalized}
          else None) in
      let interface borrow loan concrete =
        match endpoint borrow,endpoint loan with
        | Some b,Some l when b.polarity=P.Borrow && l.polarity=P.Loan ->
            Some {fixed_borrows;projectors=[b;l];concrete;history_values}
        | _ -> None in
      let concrete_leaf (concrete:tavalue) =
        let ()=phase:="ordered concrete shared-loan leaf" in
        match concrete.value,concrete.ty with
        | ALoan(ASharedLoan(PNone,_,shared,child)),
          TRef(RVar(Free region),referent,RShared)
          when RegionId.Set.mem region owner.regions.owned
            && (not (RegionId.Set.mem region excluded)
              || (RegionId.Set.mem region prefix_regions
                && RegionId.Set.mem region ctx.ended_regions))
            && ValuesUtils.is_aignored child.value
            && equal_ty shared.ty (Substitute.erase_regions referent)
            && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            && not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared) ->
            (* This may share the checked prefix's ended ghost region. Its
               live concrete ID and native sublevel still carry the permission;
               validate the exact original loan, payload and ignored child. *)
            InterpSharedPacketSignature.check_retained_shared_loan
              span ctx owner 0 concrete;
            let mask=(P.view_type (P.context_of_eval ctx) owner concrete.ty).normalized in
            Some (concrete,mask)
        | _ -> None in
      let rec concrete_leaves = function
        | [] -> Some []
        | value::rest ->
            Option.bind (concrete_leaf value) (fun concrete ->
              Option.map (fun rest -> concrete::rest) (concrete_leaves rest)) in
      (* Preserve every intermediate shared referent in its original order.
         The final matcher compares each exact typed loan, payload and child;
         repeated values remain separate concrete permissions. *)
      let ()=phase:="current root ordering" in
      match live with
      | [({value=ABorrow(ASharedBorrow(PNone,bid,_));
             ty=TRef(RVar(Free region),referent,RShared)} as borrow); loan]
          when RegionId.Set.mem region input_ghost_regions
            && not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            && plain_shared_referent bid ->
          (* A shared concrete input and its symbolic shared output observe
             the same owner lifetime group, just like a symbolic input and
             concrete intermediate loans. Keep the original input permission
             and compare its full ownership mask, never quotient the RIDs. *)
          InterpSharedPacketSignature.check_retained_shared_borrow span ctx owner 0 borrow;
          (match endpoint loan with
          | Some endpoint when endpoint.polarity=P.Loan ->
              let mask=(P.view_type (P.context_of_eval ctx) owner borrow.ty).normalized in
              Some {fixed_borrows;projectors=[endpoint];concrete=[borrow,mask];history_values}
          | _ -> None)
      | borrow::rest -> (match List.rev rest with
          | loan::reversed_concrete ->
              Option.bind (concrete_leaves (List.rev reversed_concrete))
                (interface borrow loan)
          | [] -> None)
      | [] -> None
  in
  if Option.is_none result && Sys.getenv_opt "AENEAS_TRACE_SHARED_INTERFACE_MATCH"=Some "1"
    && List.exists (fun (value:tavalue) -> match value.value,value.ty with
      | ABorrow(ASharedBorrow(PNone,_,_)),TRef(RVar(Free region),_,RShared) ->
          RegionId.Set.mem region owner.regions.owned
          && (RegionId.Set.mem region fixed_regions
            || RegionId.Set.mem region ctx.ended_regions)
      | _ -> false) owner.avalues then
    Printf.eprintf
      "FINAL_SHARED_VIEW_REJECTED owner=%s phase=%s continuation_shared=%b fixed=%s owned=%s owned_ended=%s prefix_regions=%s\nroots:\n%s\n%!"
      (AbsId.to_string owner.abs_id) !phase (continuation_is_shared ctx owner)
      (RegionId.Set.to_string None fixed_regions) (RegionId.Set.to_string None owner.regions.owned)
      (RegionId.Set.to_string None (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
      (RegionId.Set.to_string None !prefix_regions_seen)
      (String.concat "\n" (List.map show_tavalue owner.avalues));
  result

let compatible left right =
  let prefix_ok = List.length left.fixed_borrows=List.length right.fixed_borrows
    && List.for_all2 (fun (a:tavalue) (b:tavalue) ->
      equal_ty a.ty b.ty && match a.value,b.value with
      | ABorrow(ASharedBorrow(PNone,bid,_)),ABorrow(ASharedBorrow(PNone,other_bid,_)) ->
          bid=other_bid
      | _ -> false) left.fixed_borrows right.fixed_borrows in
  (* No invented identity default: each original historical value must occur
     with the same complete symbolic type in the actual target history. *)
  let history_ok = SymbolicValueId.Map.for_all (fun sid original ->
    match SymbolicValueId.Map.find_opt sid right.history_values with
    | Some actual -> equal_symbolic_value original actual
    | None -> false) left.history_values in
  let projectors_ok = List.length left.projectors=List.length right.projectors
    && List.for_all2 (fun a b ->
      a.polarity=b.polarity && equal_ty a.mask b.mask
      && equal_ty (Substitute.erase_regions a.full) (Substitute.erase_regions b.full))
        left.projectors right.projectors in
  let concrete_ok = List.length left.concrete=List.length right.concrete
    && List.for_all2 (fun ((a:tavalue),ma) ((b:tavalue),mb) ->
      equal_ty ma mb && equal_ty (Substitute.erase_regions a.ty) (Substitute.erase_regions b.ty))
        left.concrete right.concrete in
  let result=prefix_ok && history_ok && projectors_ok && concrete_ok in
  if not result && Sys.getenv_opt "AENEAS_TRACE_SHARED_INTERFACE_MATCH"=Some "1"
    && (left.fixed_borrows<>[] || right.fixed_borrows<>[]) then
    Printf.eprintf
      "FINAL_SHARED_VIEW_INCOMPATIBLE fixed_prefix=%b history=%b projectors=%b concrete=%b prefix_counts=%d,%d\nleft prefix:\n%s\nright prefix:\n%s\n%!"
      prefix_ok history_ok projectors_ok concrete_ok
      (List.length left.fixed_borrows) (List.length right.fixed_borrows)
      (String.concat "\n" (List.map show_tavalue left.fixed_borrows))
      (String.concat "\n" (List.map show_tavalue right.fixed_borrows));
  result

(** A concrete shared reborrow may retain distinct ghost lifetime names for
    two leaves even though both permissions end in the same child owner. The
    native target may use one such name. This view is confined to a complete
    two-owner shared hierarchy. Symbolic endpoint regions remain ordinary
    injective identities; only the checked concrete-only lifetime group is
    existential. No original type, permission, scope or continuation is edited. *)
type reference_family = { outer:abs; inner:abs; ghosts:RegionId.Set.t }

let concrete_reference_family span (ctx:eval_ctx) fixed_regions (owner:abs) =
  let exception Not_applicable in
  let require yes = if not yes then raise Not_applicable in
  let shared ty =
    let info=TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos ty in
    not info.contains_mut_borrow && not info.contains_static in
  let plain ty = not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos ty) in
  let split (owner:abs) = match owner.avalues with
    | ({value=ASymbolic(PNone,AProjBorrows {proj=borrow;loans=[]});_} as first)::rest ->
        (match List.rev rest with
        | ({value=ASymbolic(PNone,AProjLoans {proj=loan;consumed=[];borrows=[]});_} as last)::middle
          when middle<>[] -> first,borrow,List.rev middle,last,loan
        | _ -> raise Not_applicable)
    | _ -> raise Not_applicable in
  let find_owner aid = match List.find_opt (function EAbs abs->abs.abs_id=aid|_->false) ctx.env with
    | Some(EAbs abs)->abs | _->raise Not_applicable in
  let candidate outer =
    let first,b,leaves,last,l=split outer in
    require (outer.can_end && AbsId.Set.is_empty outer.parents
      && AbsLevelSet.is_empty outer.ended_subabs && continuation_is_shared ctx outer);
    let refs=List.map (fun (value:tavalue) -> match value.value,value.ty with
      | ALoan(ASharedLoan(PNone,_,{value=VBorrow(VSharedBorrow(bid,_));ty},child)),
        TRef(RVar(Free outer_region),(TRef(RVar(Free inner_region),target,RShared) as referent),RShared)
        when RegionId.Set.mem outer_region outer.regions.owned
          && child.value=AIgnored None && equal_ty child.ty referent
          && equal_ty ty (Substitute.erase_regions referent) && plain target ->
            value,bid,inner_region,target
      | _ -> raise Not_applicable) leaves in
    let find_loan bid =
      let found=List.concat_map (function
        | EAbs abs -> List.filter_map(fun (value:tavalue)->match value.value with
            | ALoan(ASharedLoan(PNone,lid,_,_)) when lid=bid ->Some(abs,value)
            | _->None) abs.avalues
        | _->[]) ctx.env in
      match found with [entry]->entry | _->raise Not_applicable in
    let _,first_bid,_,_=List.hd refs in
    let inner,_=find_loan first_bid in
    require (inner.can_end && AbsLevelSet.is_empty inner.ended_subabs
      && AbsId.Set.equal inner.parents (AbsId.Set.singleton outer.abs_id)
      && RegionId.Set.is_empty(RegionId.Set.inter inner.regions.owned outer.regions.owned)
      && continuation_is_shared ctx inner);
    let inner_first,ib,inner_leaves,inner_last,il=split inner in
    require (equal_symbolic_proj b ib && equal_symbolic_proj l il
      && List.length refs=List.length inner_leaves);
    let ghosts=List.fold_left2 (fun ghosts (_,bid,region,target) (leaf:tavalue) ->
      let found_owner,found_leaf=find_loan bid in
      require (found_owner.abs_id=inner.abs_id && found_leaf==leaf);
      (match leaf.value,leaf.ty with
      | ALoan(ASharedLoan(PNone,_,({value=VSymbolic sym;ty} as value),child)),
        TRef(RVar(Free leaf_region),referent,RShared) ->
          require (region=leaf_region && RegionId.Set.mem region inner.regions.owned
            && equal_ty referent target && child.value=AIgnored None
            && equal_ty child.ty referent && equal_ty sym.sv_ty referent
            && equal_ty ty (Substitute.erase_regions referent) && plain referent
            && not(InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx value))
      | _->raise Not_applicable);
      RegionId.Set.add region ghosts) RegionId.Set.empty refs inner_leaves in
    require (RegionId.Set.is_empty(RegionId.Set.inter ghosts fixed_regions)
      && RegionId.Set.is_empty(RegionId.Set.inter ghosts ctx.ended_regions));
    List.iter(fun (value:tavalue)->require(shared value.ty
      && RegionId.Set.is_empty(RegionId.Set.inter ghosts (TypesUtils.ty_regions value.ty))))
      [first;last;inner_first;inner_last];
    (* No current runtime value or third owner may observe these ghost RIDs.
       The only excluded trees are the already checked concrete loan leaves.
       Continuations remain original and were checked with native ELet scopes. *)
    let visitor=object(self)
      inherit [_] iter_env
      method! visit_region_id () rid = require(not(RegionId.Set.mem rid ghosts))
      method! visit_abs () abs =
        let values=if abs.abs_id=outer.abs_id then [first;last]
          else if abs.abs_id=inner.abs_id then [inner_first;inner_last]
          else abs.avalues in
        List.iter(self#visit_tavalue ()) values
    end in
    visitor#visit_env () ctx.env;
    (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None outer;
    (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None inner;
    {outer;inner;ghosts} in
  try
    let result=try candidate owner with Not_applicable ->
      require(AbsId.Set.cardinal owner.parents=1);
      let outer=find_owner(AbsId.Set.choose owner.parents) in
      let result=candidate outer in
      require(result.inner.abs_id=owner.abs_id);result in
    Some result
  with Not_applicable -> None

let reference_families_compatible left right =
  let masks (owner:abs) (value:tavalue) =
    InterpBorrowsCore.normalize_proj_ty owner.regions.owned value.ty in
  let compatible (a:abs) (b:abs) =
    List.length a.avalues=List.length b.avalues
    && List.for_all2(fun x y->equal_ty (masks a x) (masks b y)
      && equal_ty(Substitute.erase_regions x.ty)(Substitute.erase_regions y.ty)) a.avalues b.avalues in
  compatible left.outer right.outer && compatible left.inner right.inner

(** The non-reborrow side of a shared iterator has the same concrete-only
    lifetime group, without a child owner. Endpoint and external runtime
    regions are deliberately excluded; their ordinary injective mapping is
    still required by the caller. *)
let concrete_leaf_group span (ctx:eval_ctx) fixed_regions (owner:abs) =
  let exception Not_applicable in
  let require condition=if not condition then raise Not_applicable in
  try
    require(owner.can_end && AbsId.Set.is_empty owner.parents
      && AbsLevelSet.is_empty owner.ended_subabs && continuation_is_shared ctx owner);
    let first,last,leaves=match owner.avalues with
      | ({value=ASymbolic(PNone,AProjBorrows {loans=[];_});_} as first)::rest ->
          (match List.rev rest with
          | ({value=ASymbolic(PNone,AProjLoans {consumed=[];borrows=[];_});_} as last)::leaves
            when leaves<>[] -> first,last,List.rev leaves
          | _->raise Not_applicable)
      | _->raise Not_applicable in
    (* An immutable referent can already be a native ADT value, not only one
       symbolic leaf. Preserve its complete constructor/field tree and match
       it through the ordinary value matcher below. No concrete permission,
       bottom or borrowed symbolic type is admitted into this lifetime group. *)
    let rec plain_payload (value:tvalue) =
      not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos value.ty)
      && match value.value with
      | VLiteral _ -> true
      | VSymbolic symbolic -> equal_ty symbolic.sv_ty value.ty
      | VAdt adt -> List.for_all plain_payload adt.fields
      | _ -> false in
    let ghosts=List.fold_left(fun ghosts (leaf:tavalue)->
      match leaf.value,leaf.ty with
      | ALoan(ASharedLoan(PNone,_,shared,child)),
        TRef(RVar(Free region),referent,RShared) ->
          require(RegionId.Set.mem region owner.regions.owned
            && child.value=AIgnored None && equal_ty child.ty referent
            && equal_ty shared.ty (Substitute.erase_regions referent)
            && not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
            && plain_payload shared);
          InterpSharedPacketSignature.check_retained_shared_loan span ctx owner 0 leaf;
          RegionId.Set.add region ghosts
      | _->raise Not_applicable) RegionId.Set.empty leaves in
    require(RegionId.Set.is_empty(RegionId.Set.inter ghosts fixed_regions)
      && RegionId.Set.is_empty(RegionId.Set.inter ghosts ctx.ended_regions));
    List.iter(fun (value:tavalue)->
      let info=TypesAnalysis.analyze_ty (Some span) ctx.type_ctx.type_infos value.ty in
      require(not info.contains_mut_borrow && not info.contains_static
        && RegionId.Set.is_empty(RegionId.Set.inter ghosts (TypesUtils.ty_regions value.ty)))) [first;last];
    let visitor=object(self)
      inherit [_] iter_env
      method! visit_region_id () rid=require(not(RegionId.Set.mem rid ghosts))
      method! visit_abs () abs=
        List.iter(self#visit_tavalue ())
          (if abs.abs_id=owner.abs_id then [first;last] else abs.avalues)
    end in
    visitor#visit_env () ctx.env;
    (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None owner;
    Some ghosts
  with Not_applicable -> None

let concrete_leaf_groups_compatible (left:abs) (right:abs) =
  List.length left.avalues=List.length right.avalues
  && List.for_all2(fun (a:tavalue) (b:tavalue)->
    equal_ty (InterpBorrowsCore.normalize_proj_ty left.regions.owned a.ty)
      (InterpBorrowsCore.normalize_proj_ty right.regions.owned b.ty)
    && equal_ty (Substitute.erase_regions a.ty) (Substitute.erase_regions b.ty))
    left.avalues right.avalues
