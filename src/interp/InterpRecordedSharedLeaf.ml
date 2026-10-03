(** Default-off, typed post-merge actions for the recorded right projection.
    This is not global SID deadness or arbitrary abstraction ending. *)
open Types
open Values
open Contexts
open InterpBorrowsCore
module P = InterpPacketInterface
module C = InterpExternalPermissions
module Preserve = InterpRecordedSharedLeafPreservation

let enabled () = Sys.getenv_opt "AENEAS_EXPERIMENTAL_RECORDED_SHARED_LEAF" = Some "1"
let require span b message =
  [%cassert] span b ("Recorded shared leaf: " ^ message)

type leaf_placement = TopLevel | UnderIgnoredSharedLoan

type right_shared_leaf = {
  placement : leaf_placement;
  recorded_owner : abs_id;
  sid : symbolic_value_id;
  full_type : ty;
  owned : RegionId.Set.t;
  ended_regions : RegionId.Set.t;
  original_root_index : int;
  origin_owner : abs_id;
  origin_full_type : ty;
  origin_owned : RegionId.Set.t;
}

let shape span ctx ty =
  try C.projection_shape ~native_type_ctx:ctx.type_ctx (P.context_of_eval ctx) ty
  with C.Unsupported s -> [%craise] span ("Recorded shared leaf: type domain: " ^ s)

(** Bidirectional positional transport is a comparison only: no actual value,
    type, region, metadata or capture is renamed. Coalescing is rejected. *)
let check_transport span ctx ~left_ty ~left_owned ~left_ended
    ~right_ty ~right_owned ~right_ended =
  let ls, lr = shape span ctx left_ty and rs, rr = shape span ctx right_ty in
  require span (equal_ty ls rs && List.length lr = List.length rr)
    "transport full type shape mismatch";
  require span (RegionId.Set.subset left_owned (RegionId.Set.of_list lr)
    && RegionId.Set.subset right_owned (RegionId.Set.of_list rr))
    "transport owned regions outside complete type";
  let forward = ref RegionId.Map.empty and backward = ref RegionId.Map.empty in
  List.iter2 (fun l r ->
    let add map a b = match RegionId.Map.find_opt a !map with
      | None -> map := RegionId.Map.add a b !map
      | Some b' -> require span (b = b') "non-bijective region transport" in
    add forward l r; add backward r l;
    require span (RegionId.Set.mem l left_owned = RegionId.Set.mem r right_owned)
      "transport owned-region role mismatch";
    require span (RegionId.Set.mem l left_ended = RegionId.Set.mem r right_ended)
      "transport ended-region role mismatch") lr rr;
  let mapper = object inherit [_] map_ty
    method! visit_region () = function
      | RVar (Free r) -> RVar (Free (RegionId.Map.find r !forward))
      | _ -> [%craise] span "Recorded shared leaf: unsupported region during transport"
  end in
  require span (equal_ty (mapper#visit_ty () left_ty) right_ty)
    "transport final full type mismatch";
  require span (equal_ty (normalize_proj_ty left_owned left_ty)
    (normalize_proj_ty right_owned right_ty)) "transport normalized owned projection mismatch"

let primary_a sid = function
  | AProjLoans q -> q.proj.sv_id = sid
  | AProjBorrows q -> q.proj.sv_id = sid
  | AEndedProjLoans q -> q.proj = sid
  | AEndedProjBorrows q -> q.mvalues.consumed = sid
  | AEmpty -> false
let primary_e sid = function
  | EProjLoans q -> q.proj.sv_id = sid
  | EProjBorrows q -> q.proj.sv_id = sid
  | EEndedProjLoans q -> q.proj = sid
  | EEndedProjBorrows q -> q.mvalues.consumed = sid
  | EEmpty -> false

let count_a sid owner =
  let n = ref 0 in
  let visit = object inherit [_] iter_abs as super
    method! visit_abs_cont () _ = ()
    method! visit_aproj () p =
      if primary_a sid p then incr n; super#visit_aproj () p
    method! visit_abstract_shared_borrow () p =
      (match p with AsbProjReborrows q when q.sv_id = sid -> incr n | _ -> ());
      super#visit_abstract_shared_borrow () p
  end in
  visit#visit_abs () owner; !n

let count_e sid ctx =
  let n = ref 0 in
  let visit = object inherit [_] iter_eval_ctx as super
    method! visit_eproj () p =
      if primary_e sid p then incr n; super#visit_eproj () p
  end in
  visit#visit_eval_ctx () ctx; !n

let current_owner span ctx aid =
  let all = List.filter_map (function EAbs a when a.abs_id = aid -> Some a | _ -> None) ctx.env in
  require span (List.length all = 1) "owner not unique in complete current environment";
  let rec in_frame = function
    | [] | EFrame :: _ -> false
    | EAbs a :: _ when a.abs_id = aid -> true
    | _ :: rest -> in_frame rest in
  require span (in_frame ctx.env) "owner outside current frame";
  List.hd all

(** Exactly two supported locations. An ignored shared wrapper carries no
    consumed or given-back interface of its own; its live child is still a
    permission and must be ended by the native operation before cleanup. *)
let loan_at_root (root : tavalue) =
  let selected placement (leaf : tavalue) = match leaf.value with
    | ASymbolic (marker, AProjLoans proj) -> Some (placement, leaf, marker, proj)
    | _ -> None in
  match root.value with
  | ALoan (AIgnoredSharedLoan child) -> selected UnderIgnoredSharedLoan child
  | _ -> selected TopLevel root

let replace_leaf placement (root : tavalue) (leaf : tavalue) =
  match placement with
  | TopLevel -> leaf
  | UnderIgnoredSharedLoan -> {root with value=ALoan(AIgnoredSharedLoan leaf)}

let right_leaf_root_index (owner : abs) =
  List.find_map (fun (i,root) -> match loan_at_root root with
    | Some (_,_,PRight,_) -> Some i
    | _ -> None) (List.mapi (fun i v -> i,v) owner.avalues)

let roots sid (owner : abs) = List.filter_map (fun (i, root) ->
  match loan_at_root root with
  | Some (placement,leaf,marker,proj) when proj.proj.sv_id=sid ->
      Some (i,root,placement,leaf,marker,proj)
  | _ -> None) (List.mapi (fun i v -> i,v) owner.avalues)

let validate_leaf span ~fixed_aids ~marker ctx owner sid =
  require span (owner.kind = WithCont && owner.can_end && Option.is_some owner.cont)
    "requires endable WithCont owner with saved continuation";
  require span (not (AbsId.Set.mem owner.abs_id fixed_aids)) "fixed owner";
  require span (not (AbsLevelSet.mem 0 owner.ended_subabs)) "level zero already ended";
  require span (current_owner span ctx owner.abs_id == owner)
    "owner is not the current physical object";
  if count_a sid owner <> 1 then
    Printf.eprintf "RECORDED_SHARED_LEAF_NONUNIQUE owner=%s sid=%s\n%s\n%!"
      (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string sid)
      (InterpUtils.abs_to_string span ~with_ended:true ctx owner);
  require span (count_a sid owner = 1) "target A occurrence is not unique";
  require span (count_e sid ctx = 0) "current E projector counterpart exists";
  let xs = roots sid owner in
  require span (List.length xs = 1) "target is not a unique supported active loan";
  let i, root, placement, v, pm, q = List.hd xs in
  (match placement, root.ty with
  | TopLevel, _ -> ()
  | UnderIgnoredSharedLoan, TRef(RVar(Free outer), referent, RShared) ->
      require span (not (RegionId.Set.mem outer owner.regions.owned))
        "ignored shared wrapper owns its outer reference region";
      require span (equal_ty referent v.ty)
        "ignored shared wrapper child disagrees with its referent type"
  | UnderIgnoredSharedLoan, _ ->
      require span false "ignored shared wrapper is not a native shared reference");
  (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None
    {owner with avalues=[root];cont=None};
  require span (pm = marker) "wrong side/marker";
  require span (q.consumed = [] && q.borrows = []) "nonempty target history";
  require span (equal_ty v.ty q.proj.proj_ty) "typed root/own projector type mismatch";
  let _, regions = shape span ctx q.proj.proj_ty in
  let free = RegionId.Set.of_list regions in
  require span (not (RegionId.Set.is_empty (RegionId.Set.inter free owner.regions.owned)))
    "empty owned projection";
  require span (RegionId.Set.subset owner.regions.owned free)
    "owned region outside selected full type";
  require span (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
    "ended owned region in selected projection";
  require span (not (TypesUtils.ty_has_mut_borrow_for_region_in_set
    ctx.type_ctx.type_infos owner.regions.owned q.proj.proj_ty)) "owned mutable projection";
  i, root, placement, v, q

(** Original input lineage is calculated from the chronological merge program.
    No final marker alone is accepted as a source witness. *)
let origins span original chronological final =
  let known = ref AbsId.Map.empty in
  List.iter (function EAbs a ->
    require span (not (AbsId.Map.mem a.abs_id !known)) "duplicate original owner ID";
    known := AbsId.Map.add a.abs_id (AbsId.Set.singleton a.abs_id) !known | _ -> ()) original.env;
  let live = ref (AbsId.Set.of_list (AbsId.Map.keys !known)) in
  List.iter (fun (a, b, c) ->
    require span (AbsId.Set.mem a !live && AbsId.Set.mem b !live)
      "merge lineage reuses consumed or unavailable owner";
    require span (a <> b && a <> c && b <> c && not (AbsId.Map.mem c !known))
      "duplicate result ID or cyclic merge lineage";
    let get x = match AbsId.Map.find_opt x !known with
      | Some s -> s | None -> [%craise] span "Recorded shared leaf: missing original merge lineage" in
    let s = AbsId.Set.union (get a) (get b) in
    known := AbsId.Map.add c s !known;
    live := AbsId.Set.add c (AbsId.Set.remove a (AbsId.Set.remove b !live))) chronological;
  require span (AbsId.Set.mem final !live) "final owner was consumed by later merge";
  match AbsId.Map.find_opt final !known with
  | Some s -> s | None -> [%craise] span "Recorded shared leaf: final owner has no original lineage"

let plan_right_leaf span ~original_joined ~chronological_merges ~fixed_aids ctx owner index =
  require span (enabled ()) "feature disabled";
  let sid = match loan_at_root (List.nth owner.avalues index) with
    | Some (_,_,PRight,q) -> q.proj.sv_id
    | _ -> [%craise] span "Recorded shared leaf: selected root is not a right loan" in
  Printf.eprintf "RECORDED_SHARED_LEAF attempt owner=%s sid=%s root=%d chronological_merges=%d\n%!"
    (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string sid) index (List.length chronological_merges);
  let i, root, placement, _, _ = validate_leaf span ~fixed_aids ~marker:PRight ctx owner sid in
  require span (i = index) "selected root index mismatch";
  let lineage = origins span original_joined chronological_merges owner.abs_id in
  let candidates = List.concat_map (fun aid ->
    let a = current_owner span original_joined aid in
    List.filter_map (fun (_, (original_root : tavalue), original_placement, (v : tavalue), pm, (oq : aproj_loans)) ->
      if original_placement=placement && pm = PRight && oq.consumed = [] && oq.borrows = []
         && equal_ty v.ty oq.proj.proj_ty && count_a sid a = 1
      then Some (a, original_root.ty) else None) (roots sid a)) (AbsId.Set.elements lineage) in
  require span (List.length candidates = 1) "no unique original right leaf witness";
  let origin, origin_ty = List.hd candidates in
  check_transport span ctx ~left_ty:origin_ty ~left_owned:origin.regions.owned
    ~left_ended:original_joined.ended_regions ~right_ty:root.ty
    ~right_owned:owner.regions.owned ~right_ended:ctx.ended_regions;
  {placement; recorded_owner=owner.abs_id; sid; full_type=root.ty;
   owned=owner.regions.owned; ended_regions=ctx.ended_regions; original_root_index=i;
   origin_owner=origin.abs_id; origin_full_type=origin_ty; origin_owned=origin.regions.owned}

(** The native update is checked before restoring original unselected objects.
    Only the exact selected leaf is eliminated, using the existing predicate;
    the global cleanup is deliberately not reapplied to unrelated roots. *)
let apply_leaf span ~fixed_aids ~marker action owner ctx =
  require span (enabled ()) "action feature disabled";
  let index, original_root, placement, original, q = validate_leaf span ~fixed_aids ~marker ctx owner action.sid in
  require span (placement=action.placement) "selected leaf changed its wrapper location";
  check_transport span ctx ~left_ty:action.full_type ~left_owned:action.owned
    ~left_ended:action.ended_regions ~right_ty:original_root.ty
    ~right_owned:owner.regions.owned ~right_ended:ctx.ended_regions;
  (* Contexts.map_eval_ctx changes only env (Contexts.ml:568-575). The complete
     expected environment is independently checked below before old objects
     are retained; ordinary equality alone is intentionally insufficient. *)
  (* Failure-only dependency evidence. The native guard below remains the
     authority; a recorded leaf cannot consume any intersecting reborrow. *)
  (match lookup_intersecting_aproj_borrows_opt span true owner.regions.owned q.proj ctx with
  | None -> ()
  | Some borrowers ->
      Printf.eprintf "RECORDED_SHARED_LEAF blocked owner=%s sid=%s marker=%s\n%s\n%!"
        (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string action.sid)
        (show_proj_marker marker) (InterpUtils.abs_to_string span ~with_ended:true ctx owner);
      let trace kind (aid, ty, level) =
        Printf.eprintf "RECORDED_SHARED_LEAF blocker kind=%s owner=%s level=%d fixed=%b proj_ty=%s\n%!"
          kind (AbsId.to_string aid) level (AbsId.Set.mem aid fixed_aids)
          (InterpUtils.ty_to_string ctx ty) in
      List.iter (trace "shared") borrowers.shared_projs;
      List.iter (trace "ordinary") borrowers.non_shared_projs;
      Invariants.trace_symbolic_value span "blocked recorded shared leaf" ctx action.sid);
  let native = InterpBorrows.end_unblocked_proj_loans span owner.abs_id owner.regions.owned q.proj ctx in
  let updated = current_owner span native owner.abs_id in
  require span (List.length updated.avalues = List.length owner.avalues)
    "native update changed root count";
  require span (Preserve.same_cont owner.cont updated.cont) "native update changed saved continuation";
  let expected_leaf = {original with value=ASymbolic(marker,AEndedProjLoans {
    proj_ty=q.proj.proj_ty;proj=q.proj.sv_id;consumed=[];borrows=[]})} in
  let expected = replace_leaf placement original_root expected_leaf in
  List.iteri (fun i v -> require span
    (Preserve.same_tavalue (if i=index then expected else List.nth owner.avalues i) v)
    "native update changed unexpected A payload") updated.avalues;
  require span (equal_abs {owner with avalues=[];cont=None} {updated with avalues=[];cont=None})
    "native update changed owner fields";
  let expected_owner = {owner with avalues = List.mapi
    (fun i v -> if i=index then expected else v) owner.avalues} in
  let expected_env = List.map
    (function EAbs a when a == owner -> EAbs expected_owner | e -> e) ctx.env in
  require span (Preserve.same_env expected_env native.env)
    "native update changed an unrelated environment payload";
  require span (InterpBorrows.ended_shared_loan_is_eliminable span native (List.nth updated.avalues index))
    "native ended leaf is not eliminable";
  let avalues = List.filter_map (fun (i,v)->if i=index then None else Some v)
    (List.mapi (fun i v->i,v) owner.avalues) in
  let result_owner = {owner with avalues} in
  let env = List.map (function EAbs a when a == owner -> EAbs result_owner | e -> e) ctx.env in
  require span (List.exists (function EAbs a -> a == result_owner | _ -> false) env)
    "original physical owner not in environment";
  {ctx with env}

let apply_planned_leaf span ~fixed_aids action ctx =
  let owner = current_owner span ctx action.recorded_owner in
  let ctx = apply_leaf span ~fixed_aids ~marker:PRight action owner ctx in
  Printf.eprintf "RECORDED_SHARED_LEAF planned owner=%s sid=%s origin=%s\n%!"
    (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string action.sid) (AbsId.to_string action.origin_owner);
  ctx

let replay_right_leaf span ~resolve_owner ~fixed_aids action ctx =
  require span (enabled ()) "replay feature disabled";
  let owner = current_owner span ctx (resolve_owner action.recorded_owner) in
  Printf.eprintf "RECORDED_SHARED_LEAF replay_attempt recorded_owner=%s actual_owner=%s sid=%s\n%!"
    (AbsId.to_string action.recorded_owner) (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string action.sid);
  let ctx = apply_leaf span ~fixed_aids ~marker:PNone action owner ctx in
  Printf.eprintf "RECORDED_SHARED_LEAF replayed recorded_owner=%s actual_owner=%s sid=%s\n%!"
    (AbsId.to_string action.recorded_owner) (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string action.sid);
  ctx
