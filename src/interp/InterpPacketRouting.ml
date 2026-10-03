(** Default-off selection and routing for preserved projector packets.
    A root index is not a complete permission inventory or a cancellation proof. *)
open Types
open Values
open Contexts
module P = InterpPacketInterface

let enabled () = Sys.getenv_opt "AENEAS_EXPERIMENTAL_PACKET_MERGE" = Some "1"
let reject span message = [%craise] span ("Packet merge integration: " ^ message)
let require span condition message = [%cassert] span condition ("Packet merge integration: " ^ message)

(** This classification must be checked before every old flat merger/reorder.
    Opaque metadata/capture environments are not searched as current owners. *)
let needs_packet (owner : abs) =
  let found = ref false in
  let ignored (v : tavalue) = match v.value with AIgnored _ -> true | _ -> false in
  let visitor = object
    inherit [_] iter_abs as super
    method! visit_aproj () p =
      (match p with
       | AProjLoans p -> if p.consumed <> [] || p.borrows <> [] then found := true
       | AProjBorrows p -> if p.loans <> [] then found := true
       | AEndedProjLoans p -> if p.consumed <> [] || p.borrows <> [] then found := true
       | AEndedProjBorrows p -> if p.loans <> [] then found := true
       | AEmpty -> ());
      super#visit_aproj () p
    method! visit_eproj () p =
      (match p with
       | EProjLoans p -> if p.consumed <> [] || p.borrows <> [] then found := true
       | EProjBorrows p -> if p.loans <> [] then found := true
       | EEndedProjLoans p -> if p.consumed <> [] || p.borrows <> [] then found := true
       | EEndedProjBorrows p -> if p.loans <> [] then found := true
       | EEmpty -> ());
      super#visit_eproj () p
    method! visit_aborrow_content () p =
      (match p with
       | AProjSharedBorrow borrows -> if borrows <> [] then found := true
       | AEndedIgnoredMutBorrow b ->
           if not (ignored b.child && ignored b.given_back) then found := true
       | AEndedMutBorrow (_, c) | AIgnoredMutBorrow (_, c) ->
           if not (ignored c) then found := true
       | _ -> ());
      super#visit_aborrow_content () p
    method! visit_aloan_content () p =
      (match p with
       | AEndedIgnoredMutLoan b ->
           if not (ignored b.child && ignored b.given_back) then found := true
       | AEndedMutLoan b ->
           if not (ignored b.child && ignored b.given_back) then found := true
       | AIgnoredMutLoan (_, c) | AIgnoredSharedLoan c | AEndedSharedLoan (_, c) ->
           if not (ignored c) then found := true
       | _ -> ());
      super#visit_aloan_content () p
  end in
  visitor#visit_abs () owner;
  !found

(** Only nonempty histories need a root-only selection index. Empty projectors
    and ordinary wrappers stay on the complete legacy collector, which already
    registers their concrete permissions without flattening the owner. *)
let has_history (owner : abs) =
  let found=ref false in
  let visitor=object
    inherit [_] iter_abs as super
    method! visit_aproj () p =
      (match p with
      | AProjLoans p -> if p.consumed<>[] || p.borrows<>[] then found:=true
      | AProjBorrows p -> if p.loans<>[] then found:=true
      | AEndedProjLoans p -> if p.consumed<>[] || p.borrows<>[] then found:=true
      | AEndedProjBorrows p -> if p.loans<>[] then found:=true
      | AEmpty -> ());super#visit_aproj () p
    method! visit_eproj () p =
      (match p with
      | EProjLoans p -> if p.consumed<>[] || p.borrows<>[] then found:=true
      | EProjBorrows p -> if p.loans<>[] then found:=true
      | EEndedProjLoans p -> if p.consumed<>[] || p.borrows<>[] then found:=true
      | EEndedProjBorrows p -> if p.loans<>[] then found:=true
      | EEmpty -> ());super#visit_eproj () p
  end in visitor#visit_abs () owner;!found

let has_shared_reborrow (owner : abs) =
  let found = ref false in
  let visitor = object
    inherit [_] iter_tavalue as super
    method! visit_AProjSharedBorrow () borrows =
      if borrows <> [] then found := true;
      super#visit_AProjSharedBorrow () borrows
  end in
  List.iter (visitor#visit_tavalue ()) owner.avalues;
  !found

let has_ignored_shared_packet (owner : abs) =
  let found = ref false in
  let visitor = object (self)
    inherit [_] iter_tavalue as super
    method! visit_AIgnoredSharedLoan _ child =
      self#visit_tavalue true child
    method! visit_ASymbolic inside_shared pm proj =
      if inside_shared then found := true;
      super#visit_ASymbolic inside_shared pm proj
  end in
  (* A nested concrete shared loan retains the native concrete collection path.
     Only symbolic packets inside the ignored wrapper need this route; shared
     reborrows are independently recognized by [has_shared_reborrow]. *)
  List.iter (visitor#visit_tavalue false) owner.avalues;
  !found

(** Structured shared wrappers are preserved while the index selects their
    ordinary packet roots. Shared reborrows remain external permissions and
    are never substituted for a normal cancellation root. *)
let uses_packet_index owner =
  has_history owner || has_shared_reborrow owner || has_ignored_shared_packet owner
  || InterpSharedPacketSignature.has_retained_ended_mut_loan owner
  || InterpSharedPacketSignature.has_retained_ignored_mut_wrapper owner

let has_empty (owner : abs) =
  let found=ref false in
  let visitor=object inherit [_] iter_tavalue as super
    method! visit_aproj () p=(match p with AEmpty->found:=true|_->());super#visit_aproj () p
  end in List.iter(visitor#visit_tavalue ())owner.avalues;!found

(** Retained shared reborrows also stay outside the flat merger. A packet
    cancellation still needs its original complementary ordinary roots; a
    shared reborrow is never substituted for one of those roots. *)
let requires_merge owner = uses_packet_index owner || has_empty owner

(** Bounded observation only: these predicates are the production dispatcher
    inputs, not a pretty-printed inference about hidden history. *)
let route_trace_count = ref 0
let trace_route (left : abs) (right : abs) dispatch =
  if Sys.getenv_opt "AENEAS_TRACE_PACKET_ROUTE" = Some "1"
     && !route_trace_count < 32 then begin
    incr route_trace_count;
    prerr_endline ("PACKET_ROUTE left=" ^ AbsId.to_string left.abs_id
      ^ " right=" ^ AbsId.to_string right.abs_id
      ^ " left_history=" ^ string_of_bool (has_history left)
      ^ " right_history=" ^ string_of_bool (has_history right)
      ^ " left_empty=" ^ string_of_bool (has_empty left)
      ^ " right_empty=" ^ string_of_bool (has_empty right)
      ^ " dispatch=" ^ string_of_bool dispatch)
  end

(** Production provenance: [ctx.type_ctx] is the immutable declaration/analysis
    universe constructed by Interp.compute_contexts from the running LLBC, then
    copied unchanged into eval_ctx. Unlike the offline snapshot consumer this
    does not claim an independent second analysis; its trust is the ordinary
    compiler input/type-analysis boundary. Existing opaque admission is unchanged.
    Every retained packet is inventoried with path/level/full type. Original
    retained nodes are checked by the native type invariant; the stricter C
    comparison fragment applies only when prepare compares selected or same-SID
    external permissions, not as a new global type-admission restriction. Concrete
    live/tracked-ID permissions are rejected except explicitly retained
    checked shared leaves at their original native paths/levels: top-level,
    current ADT loan fields, or the supported ended mutable-loan wrapper. Their
    referents pass the strict shared-value/native checks. E calls/captures are
    retained; real continuation/Pure code validates them. *)
let validate_owner ?(allow_marked=false) span (ctx : eval_ctx) (owner : abs) =
  try
  let pc = P.context_of_eval ctx in
  Invariants.opt_type_check_abs span ctx owner;
  let d = P.describe_owner pc owner in
  List.iter (fun (p : P.packet) ->
    if p.polarity <> P.Empty then begin
      require span (allow_marked || p.marker=PNone)
        "marked packet admitted only for marker-aware inspection/indexing";
      require span (not p.typ.owned_mutable) "retained packet has a mutable owned projection";
      if p.phase = P.Live then begin
        require span (not (AbsLevelSet.mem p.at.level owner.ended_subabs))
          "active packet occurs at a recorded ended level";
        require span (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned p.typ.ended_regions))
          "active packet's projected owned region is ended"
      end
    end) d.packets;
  List.iter (fun (r : P.shared_reborrow) ->
    require span (r.at.surface = P.A) "shared reborrow outside current A permissions";
    match r.proj with
    | Some proj ->
        InterpSharedPacketSignature.check_shared_reborrow span ctx owner r.at.level proj
    | None -> reject span "concrete shared reborrow needs separate admission") d.shared_reborrows;
  if d.shared_reborrows <> [] then
    (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None owner;
  List.iter (fun (n : P.node) -> match n.original with
    | P.AValue v -> (match v.value with
      | ABorrow (ASharedBorrow _) ->
          require span (InterpSharedPacketSignature.retained_shared_leaf_path span ctx owner n.path n.level v)
            "retained concrete shared borrow is outside a supported typed root";
          InterpSharedPacketSignature.check_retained_shared_borrow ~allow_marked span ctx owner n.level v
      | ALoan (ASharedLoan _) ->
          require span (InterpSharedPacketSignature.retained_shared_leaf_path span ctx owner n.path n.level v)
            "retained concrete shared loan is outside a supported typed root";
          InterpSharedPacketSignature.check_retained_shared_loan ~allow_marked span ctx owner n.level v
      | ABorrow (AIgnoredMutBorrow (Some bid,child)) ->
          InterpSharedPacketSignature.check_tracked_ignored_mut_borrow ~allow_marked
            span ctx owner n.level bid v.ty child.ty
      | ALoan (AIgnoredMutLoan (Some bid,child)) ->
          InterpSharedPacketSignature.check_tracked_ignored_mut_loan ~allow_marked
            span ctx owner n.level bid v.ty child.ty
      | ABorrow (AMutBorrow _)
      | ALoan (AMutLoan _) ->
          reject span ("current concrete/tracked ignored permission in packet owner "
            ^ AbsId.to_string owner.abs_id ^ " at " ^ String.concat "/" n.path
            ^ " (history=" ^ string_of_bool (has_history owner)
            ^ ", shared_reborrow=" ^ string_of_bool (has_shared_reborrow owner)
            ^ ", ignored_shared_packet=" ^ string_of_bool (has_ignored_shared_packet owner)
            ^ "): " ^ InterpUtils.tavalue_to_string ~with_ended:true ctx v
            ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner)
      | ALoan (AEndedSharedLoan (sv,_)) ->
          require span (not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx sv))
            "ended shared stored value still has current borrow/loan permissions"
      | _ -> ())
    | P.EValue v -> (match v.value with
      | EBorrow (EIgnoredMutBorrow (Some bid,child)) ->
          InterpSharedPacketSignature.check_tracked_ignored_mut_borrow ~allow_marked
            span ctx owner n.level bid v.ty child.ty
      | ELoan (EIgnoredMutLoan (Some bid,child)) ->
          InterpSharedPacketSignature.check_tracked_ignored_mut_loan ~allow_marked
            span ctx owner n.level bid v.ty child.ty
      | EBorrow (EMutBorrow _)
      | ELoan (EMutLoan _) ->
          reject span ("current E concrete/tracked ignored permission in packet owner "
            ^ AbsId.to_string owner.abs_id ^ " at " ^ String.concat "/" n.path
            ^ ": " ^ InterpUtils.tevalue_to_string ~with_ended:true ctx v
            ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner)
      | _ -> ())
    | _ -> ()) d.nodes;
  d
  with error ->
    let backtrace=Printexc.get_raw_backtrace () in
    Printf.eprintf "PACKET_OWNER_VALIDATION_REJECTED marker_aware=%b ended_regions=%s\n%s\n%!"
      allow_marked (RegionId.Set.to_string None ctx.ended_regions)
      (InterpUtils.abs_to_string span ~with_ended:true ctx owner);
    Printexc.raise_with_backtrace error backtrace

(** Empty placeholders can coexist with retained live permissions after a
    packet cancellation. Preserve the exact owner and continuation, including
    their order; this path admits no additional cancellation. The ordinary
    collector ignores AEmpty but still registers the remaining level-zero live
    projectors. Structured shared permissions use the packet index instead. *)
let validate_empty_order ?(allow_marked=false) span ctx owner =
  let d=validate_owner ~allow_marked span ctx owner in
  require span (has_empty owner && not(has_history owner))
    "empty-preserving reorder requires an empty node and no history";
  if not (uses_packet_index owner) then
    List.iter (fun (p:P.packet) ->
      if p.at.surface=P.A && p.phase=P.Live then
        require span (p.at.level=0)
          "empty-preserving legacy index has a non-root live projector") d.packets

let roots (d : P.descriptor) =
  List.filter (fun (p : P.packet) ->
    p.at.surface = P.A && p.at.level = 0 && p.phase = P.Live) d.packets

let complementary_pairs ~allow_marked span (ld : P.descriptor) (bd : P.descriptor) =
  let pairs = List.concat_map (fun (l : P.packet) ->
    if l.polarity <> P.Loan then [] else
      List.filter_map (fun (b : P.packet) ->
        if b.polarity = P.Borrow && l.marker = b.marker && l.sid = b.sid
           && equal_ty l.typ.normalized b.typ.normalized
        then Some (l,b) else None) (roots bd)) (roots ld) in
  match pairs with
  | [] -> reject span "no level-zero complementary packet for selected owners"
  | [_] -> pairs
  | _ ->
      (* A branch join can expose separate left/right ordinary edges between
         the same owners. They are independent only with distinct SIDs and
         original endpoints; each still needs its own complete closure check.
         Histories and overlapping candidate choices remain unsupported. *)
      require span (allow_marked && List.for_all (fun (loan,borrow) ->
        loan.P.marker<>PNone && match P.original_ap loan,P.original_ap borrow with
        | AProjLoans {consumed=[];borrows=[];_},AProjBorrows {loans=[];_} -> true
        | _ -> false) pairs)
        "multiple packet edges require marked history-free ordinary roots";
      let distinct project =
        let keys=List.map project pairs in
        List.length keys=List.length (List.sort_uniq Stdlib.compare keys) in
      require span (distinct (fun ((loan:P.packet),_) -> loan.sid)
        && distinct (fun ((loan:P.packet),_) -> loan.at.path)
        && distinct (fun (_,(borrow:P.packet)) -> borrow.at.path))
        "ambiguous or dependent level-zero complementary packet selection";
      pairs

(** The ordinary native shared-edge merge removes a right borrow when its
    loan is retained on the left. It does not cancel either owner's symbolic
    projector. The native rule compares the exact marker as part of the
    permission identity; collapse selects only explicitly marked edges.
    Restrict this path to one unambiguous right borrow root. In an unmarked
    context its loan may remain under checked level-zero native ADT fields;
    the existing merge retains that entire original left tree. *)
let shared_edge ?(allow_marked=false) ?(allow_symbolic_pair=false) span (left : P.descriptor) (right : P.descriptor) =
  let pairs (loan_owner : P.descriptor) (borrow_owner : P.descriptor) =
    let loans = List.filter_map (fun (node : P.node) -> match node.original with
      | P.AValue ({value=ALoan(ASharedLoan _);_} as loan)
        when node.level=0
          && ((match node.path with ["avalue";_] -> true | _ -> false)
            || (not allow_marked
              && Option.is_some
                (InterpSharedPacketSignature.retained_adt_shared_loan_root
                  loan_owner.owner node.path node.level loan))) -> Some loan
      | _ -> None) loan_owner.nodes in
    List.concat_map (fun (loan : tavalue) -> match loan.value with
      | ALoan (ASharedLoan (marker, bid, _, _))
        when (if allow_marked then marker<>PNone else marker=PNone) ->
          List.filter_map (fun (borrow : tavalue) -> match borrow.value with
            | ABorrow (ASharedBorrow (borrow_marker, bid', sid))
              when marker=borrow_marker && bid = bid' ->
                Some (loan, borrow, bid, sid)
            | _ -> None) borrow_owner.owner.avalues
      | _ -> []) loans
  in
  match pairs left right with
  | [] -> None
  | [edge] ->
      require span (pairs right left = [])
        "concrete shared merge has a reverse internal edge";
      let symbolic_pair a b = List.exists (fun (loan : P.packet) ->
        loan.polarity = P.Loan && List.exists (fun (borrow : P.packet) ->
          borrow.polarity = P.Borrow && loan.marker = borrow.marker && loan.sid = borrow.sid
          && equal_ty loan.typ.normalized borrow.typ.normalized) (roots b)) (roots a) in
      let symbolic_forward=symbolic_pair left right
      and symbolic_reverse=symbolic_pair right left in
      if symbolic_reverse || (symbolic_forward && not allow_symbolic_pair) then
        Printf.eprintf "MIXED_SHARED_EDGE_REJECTED forward=%b reverse=%b\nleft:\n%s\nright:\n%s\n%!"
          symbolic_forward symbolic_reverse (show_abs left.owner) (show_abs right.owner);
      require span (not symbolic_reverse && (not symbolic_forward || allow_symbolic_pair))
        "concrete shared merge also requires symbolic cancellation";
      Some edge
  | _ -> reject span "ambiguous concrete shared merge edges"

(** A normal branch collapse may select two copies of the same current
    interface, rather than a loan/borrow cancellation edge. Limit this route to
    complementary flat shared interfaces; analysis may retain independent
    symbolic loan outputs. Historical roots must have
    no current permission and no mutable interface at any native level; they
    stay in the result as their original objects. *)
let shared_duplicate_interface ?(allow_residual_loans=false) span ctx (left:abs) (right:abs) =
  let owned=RegionId.Set.union left.regions.owned right.regions.owned in
  let history owner value =
    InterpSharedHistory.permission_free_history span ctx value
    && InterpSharedHistory.empty_native_interface span ctx owner value in
  let left_history,left_live=List.partition (history left) left.avalues
  and right_history,right_live=List.partition (history right) right.avalues in
  let marker (value:tavalue)=match value.value with
    | ABorrow(ASharedBorrow(pm,_,_)) | ALoan(ASharedLoan(pm,_,_,_))
    | ASymbolic(pm,_) -> Some pm | _ -> None in
  let flat (value:tavalue)=match value.value with
    | ABorrow(ASharedBorrow _) ->
        (match value.ty with TRef(_,referent,RShared) ->
          not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos referent)
        | _ -> false)
    | ALoan(ASharedLoan(_,_,shared,child)) ->
        ValuesUtils.is_aignored child.value
        && not(TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos shared.ty)
        && not(InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared)
    | ASymbolic(_,AProjBorrows {proj;loans=[]})
    | ASymbolic(_,AProjLoans {proj;consumed=[];borrows=[]}) ->
        equal_ty value.ty proj.proj_ty
        && not(TypesUtils.ty_has_mut_borrow_for_region_in_set
          ctx.type_ctx.type_infos owned proj.proj_ty)
    | _ -> false in
  let same_key (a:tavalue) (b:tavalue)=
    equal_ty (InterpBorrowsCore.normalize_proj_ty owned a.ty) (InterpBorrowsCore.normalize_proj_ty owned b.ty)
    && match a.value,b.value with
    | ABorrow(ASharedBorrow(_,a,_)),ABorrow(ASharedBorrow(_,b,_)) -> a=b
    | ALoan(ASharedLoan(_,a,_,_)),ALoan(ASharedLoan(_,b,_,_)) -> a=b
    | ASymbolic(_,AProjBorrows a),ASymbolic(_,AProjBorrows b) -> a.proj.sv_id=b.proj.sv_id
    | ASymbolic(_,AProjLoans a),ASymbolic(_,AProjLoans b) -> a.proj.sv_id=b.proj.sv_id
    | _ -> false in
  let complementary a b=match marker a,marker b with
    | Some PLeft,Some PRight | Some PRight,Some PLeft -> true | _ -> false in
  let unique roots=List.for_all (fun root ->
    List.length(List.filter(same_key root) roots)=1) roots in
  let complete = left_live<>[] && List.length left_live=List.length right_live
    && List.for_all2 (fun a b -> same_key a b && complementary a b) left_live right_live in
  (* Analysis collapse can join one shared input while the two branches retain
     different shared outputs. These outputs are not cancellation candidates:
     every residual is an original history-free loan with a SID distinct from
     every other current root. Only complementary borrows are merged. Keep the
     recorded/synthesis classifier on the complete-interface case above. *)
  let partial = allow_residual_loans &&
    let all=left_live@right_live in
    let borrowed (value:tavalue)=match value.value with
      | ASymbolic(_,AProjBorrows {loans=[];_}) -> true | _ -> false in
    let same_side roots pm=List.for_all (fun value -> marker value=Some pm) roots in
    let supported roots other=List.for_all (fun (value:tavalue) ->
      match value.value with
      | ASymbolic(_,AProjBorrows {loans=[];_}) ->
          (match List.filter (same_key value) other with
          | [paired] -> complementary value paired && equal_ty value.ty paired.ty
          | _ -> false)
      | ASymbolic(_,AProjLoans {proj;consumed=[];borrows=[]}) ->
          List.length(List.filter (fun (candidate:tavalue) -> match candidate.value with
            | ASymbolic(_,AProjBorrows {proj=other;_})
            | ASymbolic(_,AProjLoans {proj=other;_}) -> proj.sv_id=other.sv_id
            | _ -> false) all)=1
      | _ -> false) roots in
    List.exists borrowed left_live
    && ((same_side left_live PLeft && same_side right_live PRight)
      || (same_side left_live PRight && same_side right_live PLeft))
    && supported left_live right_live && supported right_live left_live in
  if (complete || partial) && List.for_all flat (left_live@right_live)
    && unique left_live && unique right_live
  then Some(left_history,right_history,left_live,right_live,flat,same_key,marker)
  else None

(** A typed companion to a legacy merge triple. The right projection can
    remove earlier roots, so replay identifies endpoints by their original SID,
    polarity, complete type and normalized permission mask, never a root index.
    An independent left pair may disappear under projection; it is checked
    separately before recording the unique surviving right pair. *)
type recorded_right_pair = {
  sid : symbolic_value_id;
  loan_type : ty;
  borrow_type : ty;
  loan_mask : ty;
  borrow_mask : ty;
  ended_regions : RegionId.Set.t;
  fixed_aids : AbsId.Set.t;
}

let ordinary_right_pair span ctx left right =
  let ld=validate_owner ~allow_marked:true span ctx left
  and bd=validate_owner ~allow_marked:true span ctx right in
  require span (shared_edge ~allow_marked:true span ld bd=None)
    "recorded packet merge has a concrete shared edge";
  let pairs=complementary_pairs ~allow_marked:true span ld bd in
  let right_pairs=match pairs with
    | [_] -> pairs
    | [first;second] ->
        (* The existing original merge checks and cancels both disjoint roots.
           Right projection removes the entire independent left pair, so only
           the uniquely identified right pair is part of replay. *)
        List.iter (fun ((loan:P.packet),(borrow:P.packet)) ->
          require span (loan.marker=borrow.marker
            && (loan.marker=PLeft || loan.marker=PRight)
            && not loan.typ.owned_mutable && not borrow.typ.owned_mutable)
            "recorded dual packet merge has a non-shared or unmarked endpoint";
          match P.original_ap loan,P.original_ap borrow with
          | AProjLoans {consumed=[];borrows=[];_}, AProjBorrows {loans=[];_} -> ()
          | _ -> reject span "recorded dual packet merge has selected history") [first;second];
        List.filter (fun ((loan:P.packet),_) -> loan.marker=PRight) pairs
    | _ -> reject span "recorded packet merge has more than two selected edges" in
  match right_pairs with
  | [loan,borrow] ->
      require span (loan.P.marker=PRight && borrow.P.marker=PRight
        && not loan.typ.owned_mutable && not borrow.typ.owned_mutable)
        "recorded packet merge requires one right shared edge";
      (match P.original_ap loan,P.original_ap borrow with
      | AProjLoans {consumed=[];borrows=[];_}, AProjBorrows {loans=[];_} -> ()
      | _ -> reject span "recorded selected packet has nested history");
      loan,borrow
  | _ -> reject span "recorded packet merge has multiple selected edges"

let record_right_pair span ctx ~fixed_aids left right =
  let loan,borrow=ordinary_right_pair span ctx left right in
  {sid=Option.get loan.P.sid;loan_type=loan.typ.full;borrow_type=borrow.typ.full;
   loan_mask=loan.typ.normalized;borrow_mask=borrow.typ.normalized;
   ended_regions=ctx.ended_regions;fixed_aids}

(** Projection can remove a left-only owner from an earlier legacy merge.
    The right replay then keeps its own lifetime names instead of that merge's
    global quotient representative. Compare both endpoints with one shared
    bijection: duplicate aliases and ended-region roles must remain identical.
    This is a read-only comparison; current full types and masks stay native. *)
let endpoint_types_match span (ctx:eval_ctx) expected_ended expected_types
    actual_types expected_masks actual_masks =
  let canonical ended types =
    let regions=ref RegionId.Map.empty and next=ref 0 and roles=ref [] in
    let visitor=object
      inherit [_] map_ty
      method! visit_region () = function
        | RVar (Free region) ->
            roles := RegionId.Set.mem region ended :: !roles;
            let id=match RegionId.Map.find_opt region !regions with
              | Some id -> id
              | None ->
                  let id=RegionId.of_int !next in incr next;
                  regions:=RegionId.Map.add region id !regions;id in
            RVar (Free id)
        | RStatic -> RStatic
        | _ -> reject span "right packet replay has a non-free region"
    end in
    let types=List.map (visitor#visit_ty ()) types in
    types,List.rev !roles in
  canonical expected_ended expected_types = canonical ctx.ended_regions actual_types
  && List.for_all2 equal_ty expected_masks actual_masks

let right_pair_types_match span (ctx:eval_ctx) (action:recorded_right_pair)
    (loan:P.packet) (borrow:P.packet) =
  endpoint_types_match span ctx action.ended_regions
    [action.loan_type;action.borrow_type] [loan.typ.full;borrow.typ.full]
    [action.loan_mask;action.borrow_mask] [loan.typ.normalized;borrow.typ.normalized]

let validate_right_replay span ctx action left right =
  let ld=validate_owner span ctx left and bd=validate_owner span ctx right in
  require span (shared_edge span ld bd=None)
    "right packet replay acquired a concrete shared edge";
  match complementary_pairs ~allow_marked:false span ld bd with
  | [loan,borrow] ->
      let same_types=right_pair_types_match span ctx action loan borrow in
      if loan.P.sid<>Some action.sid || borrow.P.sid<>Some action.sid || not same_types then
        Printf.eprintf "RECORDED_PACKET_ENDPOINT_CHANGED sid=%s loan_sid=%s borrow_sid=%s markers=%s,%s\nexpected loan=%s\nexpected borrow=%s\nexpected masks=%s / %s\nactual loan=%s\nactual borrow=%s\nactual masks=%s / %s\nleft:\n%s\nright:\n%s\n%!"
          (SymbolicValueId.to_string action.sid)
          (Option.fold ~none:"none" ~some:SymbolicValueId.to_string loan.sid)
          (Option.fold ~none:"none" ~some:SymbolicValueId.to_string borrow.sid)
          (show_proj_marker loan.marker) (show_proj_marker borrow.marker)
          (show_ty action.loan_type) (show_ty action.borrow_type)
          (show_ty action.loan_mask) (show_ty action.borrow_mask)
          (show_ty loan.typ.full) (show_ty borrow.typ.full)
          (show_ty loan.typ.normalized) (show_ty borrow.typ.normalized)
          (InterpUtils.abs_to_string span ~with_ended:true ctx left)
          (InterpUtils.abs_to_string span ~with_ended:true ctx right);
      require span (loan.P.marker=PNone && borrow.P.marker=PNone
        && loan.sid=Some action.sid && borrow.sid=Some action.sid
        && same_types)
        "right packet replay changed endpoint identity, full type or projection mask";
      (match P.original_ap loan,P.original_ap borrow with
      | AProjLoans {consumed=[];borrows=[];_}, AProjBorrows {loans=[];_} -> ()
      | _ -> reject span "right packet replay acquired selected history")
  | _ -> reject span "right packet replay lost its unique recorded edge"

(** If an exact left concrete edge disappears under the right projection,
    replay composes its retained historical owner with the right owner without
    selecting a replacement edge. This is distinct from cancellation. *)
type vanished_left_shared = {
  loan_id:loan_id; shared_id:shared_borrow_id; fixed_aids:AbsId.Set.t;
}
type recorded_right_shared = {
  loan_id:loan_id; shared_id:shared_borrow_id;
  loan_type:ty; borrow_type:ty; loan_mask:ty; borrow_mask:ty;
  ended_regions:RegionId.Set.t; fixed_aids:AbsId.Set.t;
}
(** Right projection of a complete complementary shared interface keeps only
    the right permissions. The left owner can still carry historical trees and
    its original continuation, so replay composes the projected owners without
    selecting a new cancellation edge. *)
type duplicate_root_key =
  | SharedBorrowKey of borrow_id * shared_borrow_id
  | SharedLoanKey of loan_id
  | SymbolicBorrowKey of symbolic_value_id
  | SymbolicLoanKey of symbolic_value_id

type recorded_interface_root = {
  key:duplicate_root_key; full:ty; mask:ty;
  payload:(tvalue * tavalue) option;
}
type vanished_left_interface = {
  right_roots:recorded_interface_root list;
  left_has_cont:bool; right_has_cont:bool;
  ended_regions:RegionId.Set.t; fixed_aids:AbsId.Set.t;
}

let interface_root span ctx owner (value:tavalue) =
  let marker,key,payload=match value.value with
    | ABorrow(ASharedBorrow(pm,bid,sid)) -> pm,SharedBorrowKey(bid,sid),None
    | ALoan(ASharedLoan(pm,bid,shared,child)) -> pm,SharedLoanKey bid,Some(shared,child)
    | ASymbolic(pm,AProjBorrows {proj;loans=[]}) -> pm,SymbolicBorrowKey proj.sv_id,None
    | ASymbolic(pm,AProjLoans {proj;consumed=[];borrows=[]}) -> pm,SymbolicLoanKey proj.sv_id,None
    | _ -> reject span "recorded shared interface acquired another root kind" in
  let view=P.view_type (P.context_of_eval ctx) owner value.ty in
  marker,{key;full=view.full;mask=view.normalized;payload}

let shared_history span ctx owner value =
  InterpSharedHistory.permission_free_history span ctx value
  && InterpSharedHistory.empty_native_interface span ctx owner value

type recorded_merge =
  | RightPair of recorded_right_pair
  | RightShared of recorded_right_shared
  | VanishedLeftShared of vanished_left_shared
  | VanishedLeftInterface of vanished_left_interface

let recorded_fixed = function
  | RightPair a->a.fixed_aids | RightShared a->a.fixed_aids | VanishedLeftShared a->a.fixed_aids
  | VanishedLeftInterface a->a.fixed_aids
let recorded_description = function
  | RightPair a -> "sid=" ^ SymbolicValueId.to_string a.sid
  | RightShared a -> "right_shared_loan=" ^ BorrowId.to_string a.loan_id
  | VanishedLeftShared a -> "vanished_left_loan=" ^ BorrowId.to_string a.loan_id
  | VanishedLeftInterface a -> "right_interface_roots=" ^ string_of_int(List.length a.right_roots)

let right_shared_types span (ctx:eval_ctx) left right (loan:tavalue) (borrow:tavalue) =
  (match loan.value with
  | ALoan(ASharedLoan(_,_,shared,child)) ->
      require span (ValuesUtils.is_aignored child.value
        && not (TypesUtils.ty_has_borrows (Some span) ctx.type_ctx.type_infos shared.ty)
        && not (InterpUtils.tvalue_has_loans_or_borrows (Some span) ctx shared))
        "recorded right shared edge has a nested referent permission"
  | _ -> reject span "recorded right shared endpoint is not a shared loan");
  let pc=P.context_of_eval ctx in
  P.view_type pc left loan.ty,P.view_type pc right borrow.ty

let record_merge span ctx ~fixed_aids left right =
  let ld=validate_owner ~allow_marked:true span ctx left
  and rd=validate_owner ~allow_marked:true span ctx right in
  match shared_edge ~allow_marked:true span ld rd with
  | None -> (match shared_duplicate_interface span ctx left right with
      | None -> RightPair (record_right_pair span ctx ~fixed_aids left right)
      | Some(_,_,left_live,right_live,_,_,marker) ->
          require span (List.for_all (fun v->marker v=Some PLeft) left_live
            && List.for_all (fun v->marker v=Some PRight) right_live)
            "recorded duplicate interface is not a complete left/right pair";
          List.iter (fun (owner:abs) ->
            require span (Option.is_none owner.cont
              || InterpSharedInterfaceMatch.continuation_is_shared ctx owner)
              "recorded duplicate interface has an operative mutable continuation") [left;right];
          let right_roots=List.map (fun v->snd(interface_root span ctx right v)) right_live in
          VanishedLeftInterface {right_roots;
            left_has_cont=Option.is_some left.cont;right_has_cont=Option.is_some right.cont;
            ended_regions=ctx.ended_regions;fixed_aids})
  | Some (({value=ALoan(ASharedLoan(PRight,_,_,_));_} as loan),borrow,loan_id,shared_id) ->
      let loan_ty,borrow_ty=right_shared_types span ctx left right loan borrow in
      RightShared {loan_id;shared_id;loan_type=loan_ty.full;borrow_type=borrow_ty.full;
        loan_mask=loan_ty.normalized;borrow_mask=borrow_ty.normalized;
        ended_regions=ctx.ended_regions;fixed_aids}
  | Some ({value=ALoan(ASharedLoan(PLeft,_,_,_));_},_,loan_id,shared_id) ->
      (* The actual source owner contains only left current permissions and
         retained ended history. Its loop continuation is preserved exactly. *)
      require span (List.for_all (fun (p:P.packet) ->
        p.at.surface<>P.A || p.phase<>P.Live || p.marker=PLeft) ld.packets)
        "vanished-left shared owner has another live symbolic side";
      List.iter (fun (node:P.node) -> match node.original with
        | P.AValue {value=ALoan(ASharedLoan(pm,_,_,_));_}
        | P.AValue {value=ABorrow(ASharedBorrow(pm,_,_));_} ->
            require span (pm=PLeft) "vanished-left shared owner has another concrete side"
        | P.AValue {value=ABorrow(AProjSharedBorrow (_::_)
              | AIgnoredMutBorrow(Some _,_));_}
        | P.AValue {value=ALoan(AIgnoredMutLoan(Some _,_));_} ->
            reject span "vanished-left shared owner has a retained current subscription"
        | _ -> ()) ld.nodes;
      (* Native Pure classification only accepts unmarked syntax. Markers have
         already been checked above as the original permission identities;
         erase them in a temporary read-only classification value, never in
         the runtime owner, descriptors, or recorded cancellation selection. *)
      let classifier_view = object
        inherit [_] map_tavalue
        method! visit_proj_marker () _ = PNone
      end in
      require span (List.for_all (fun value ->
        InterpSharedHistory.empty_native_interface span ctx left
          (classifier_view#visit_tavalue () value)) left.avalues
        && InterpSharedInterfaceMatch.continuation_is_shared ctx left)
        "vanished-left shared owner has a mutable Pure interface";
      require span (match left.cont with
        | Some {input=Some {value=EApp(ELoop(aid,_),_);_};_} -> aid=left.abs_id
        | _ -> false) "vanished-left shared owner is not its original loop continuation";
      VanishedLeftShared {loan_id;shared_id;fixed_aids}
  | Some _ -> reject span "recorded concrete edge is outside the left-only loop rule"

let validate_merge_replay span ctx action left right =
  match action with
  | RightPair action -> validate_right_replay span ctx action left right
  | RightShared action ->
      let ld=validate_owner span ctx left and rd=validate_owner span ctx right in
      (match shared_edge span ld rd with
      | Some (loan,borrow,loan_id,shared_id) ->
          let lt,bt=right_shared_types span ctx left right loan borrow in
          require span (loan_id=action.loan_id && shared_id=action.shared_id
            && endpoint_types_match span ctx action.ended_regions
              [action.loan_type;action.borrow_type] [lt.full;bt.full]
              [action.loan_mask;action.borrow_mask] [lt.normalized;bt.normalized])
            "right shared replay changed original identity, full type or projection mask"
      | None -> reject span "right shared replay lost its original concrete edge")
  | VanishedLeftInterface action ->
      ignore(validate_owner span ctx left);ignore(validate_owner span ctx right);
      require span (Option.is_some left.cont=action.left_has_cont
        && Option.is_some right.cont=action.right_has_cont)
        "projected duplicate interface changed continuation presence";
      require span (List.for_all (shared_history span ctx left) left.avalues)
        "projected duplicate left interface still has a current permission";
      List.iter (fun (owner:abs) ->
        require span (Option.is_none owner.cont
          || InterpSharedInterfaceMatch.continuation_is_shared ctx owner)
          "projected duplicate interface acquired a mutable continuation") [left;right];
      let live=List.filter (fun v->not(shared_history span ctx right v)) right.avalues in
      let roots=List.map (interface_root span ctx right) live in
      require span (List.length roots=List.length action.right_roots
        && List.for_all (fun (marker,_)->marker=PNone) roots)
        "projected duplicate right interface changed root count or markers";
      let actual=List.map snd roots in
      require span (List.for_all2 (fun expected actual ->
        expected.key=actual.key && match expected.payload,actual.payload with
        | None,None -> true
        | Some(sv,child),Some(actual_sv,actual_child) ->
            equal_tvalue sv actual_sv && InterpSharedHistory.same_complete_value child actual_child
        | _ -> false) action.right_roots actual)
        "projected duplicate interface changed a permission ID or shared payload";
      require span (endpoint_types_match span ctx action.ended_regions
        (List.map(fun root->root.full) action.right_roots) (List.map(fun root->root.full) actual)
        (List.map(fun root->root.mask) action.right_roots) (List.map(fun root->root.mask) actual))
        "projected duplicate interface changed full types or projection masks"
  | VanishedLeftShared action ->
      ignore (validate_owner span ctx left);ignore (validate_owner span ctx right);
      require span (List.for_all (fun value ->
        InterpSharedHistory.permission_free_history span ctx value
        && InterpSharedHistory.empty_native_interface span ctx left value) left.avalues
        && InterpSharedInterfaceMatch.continuation_is_shared ctx left)
        "projected left owner retains a current permission or mutable Pure interface";
      let gone=ref true in
      let visitor=object
        inherit [_] iter_tavalue
        method! visit_ASharedBorrow () _ bid sid =
          if bid=action.loan_id && sid=action.shared_id then gone:=false
      end in
      List.iter (visitor#visit_tavalue ()) right.avalues;
      require span !gone "selected left shared borrow survived right projection"

(** Only regular current-frame parent edges are remapped. Captured environments,
    continuation IDs, metadata and the removed owner's payload are unchanged. *)
let remap_borrower_parents old_id new_id (ctx : eval_ctx) =
  let rec visit = function
    | [] -> []
    | EFrame :: _ as rest -> rest
    | EAbs a :: rest ->
        let a = if a.abs_id <> old_id && AbsId.Set.mem old_id a.parents then
          {a with parents=AbsId.Set.add new_id (AbsId.Set.remove old_id a.parents)}
          else a in
        EAbs a :: visit rest
    | binding :: rest -> binding :: visit rest
  in {ctx with env=visit ctx.env}

(** Validate the original frame and prospective parent contraction before any
    fresh allocation. Combining two nodes must not create a cycle through a
    retained owner. This is a rejection check, not parent-edge deletion. *)
let check_parent_commit span (ctx : eval_ctx) left right parents =
  let rec frame = function
    | [] | EFrame :: _ -> []
    | EAbs a :: rest -> a :: frame rest
    | _ :: rest -> frame rest in
  let owners=frame ctx.env in
  List.iter (fun original ->
    require span (List.exists (fun a -> a==original) owners)
      "packet owners must occur in the current frame") [left;right];
  let rec walk seen id =
    require span (id<>left.abs_id && id<>right.abs_id)
      "packet parent contraction would create a cycle";
    if not (AbsId.Set.mem id seen) then begin
      let a=match env_lookup_abs_opt ctx.env id with
        | Some a -> a | None -> reject span "packet parent graph has a missing owner" in
      let seen=AbsId.Set.add id seen in
      AbsId.Set.iter (walk seen) a.parents
    end in
  AbsId.Set.iter (walk AbsId.Set.empty) parents
