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
    top-level shared leaves with borrow-free referents and native loan checks.
    E calls/captures are retained; real continuation/Pure code validates them. *)
let validate_owner span (ctx : eval_ctx) (owner : abs) =
  let pc = P.context_of_eval ctx in
  Invariants.opt_type_check_abs span ctx owner;
  let d = P.describe_owner pc owner in
  List.iter (fun (p : P.packet) ->
    if p.polarity <> P.Empty then begin
      require span (not p.typ.owned_mutable) "retained packet has a mutable owned projection";
      if p.phase = P.Live then begin
        require span (not (AbsLevelSet.mem p.at.level owner.ended_subabs))
          "active packet occurs at a recorded ended level";
        require span (RegionId.Set.is_empty (RegionId.Set.inter owner.regions.owned ctx.ended_regions))
          "active packet owner region is ended"
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
          require span (match n.path with ["avalue"; _] -> true | _ -> false)
            "retained concrete shared borrow must be a top-level root";
          InterpSharedPacketSignature.check_retained_shared_borrow span ctx owner n.level v
      | ALoan (ASharedLoan _) ->
          require span (match n.path with ["avalue"; _] -> true | _ -> false)
            "retained concrete shared loan must be a top-level root";
          InterpSharedPacketSignature.check_retained_shared_loan span ctx owner n.level v
      | ABorrow (AMutBorrow _ | AIgnoredMutBorrow (Some _, _))
      | ALoan (AMutLoan _ | AIgnoredMutLoan (Some _, _)) ->
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
      | EBorrow (EMutBorrow _ | EIgnoredMutBorrow (Some _, _))
      | ELoan (EMutLoan _ | EIgnoredMutLoan (Some _, _)) ->
          reject span ("current E concrete/tracked ignored permission in packet owner "
            ^ AbsId.to_string owner.abs_id ^ " at " ^ String.concat "/" n.path
            ^ ": " ^ InterpUtils.tevalue_to_string ~with_ended:true ctx v
            ^ "\n" ^ InterpUtils.abs_to_string span ~with_ended:true ctx owner)
      | _ -> ())
    | _ -> ()) d.nodes;
  d

(** Empty packet roots do not imply an absence of retained shared reborrows.
    Validate those separately and preserve the exact owner and continuation;
    this ordering path is not a cancellation admission. *)
let validate_empty_order span ctx owner =
  let d=validate_owner span ctx owner in
  require span (has_empty owner && not(has_history owner))
    "empty-only reorder requires an empty node and no history";
  require span (not(List.exists(fun(p:P.packet)->p.at.surface=P.A && p.phase=P.Live)d.packets))
    "empty-only reorder cannot hide residual live projectors"

let roots (d : P.descriptor) =
  List.filter (fun (p : P.packet) ->
    p.at.surface = P.A && p.at.level = 0 && p.phase = P.Live) d.packets

let unique_pair span (ld : P.descriptor) (bd : P.descriptor) =
  let pairs = List.concat_map (fun (l : P.packet) ->
    if l.polarity <> P.Loan then [] else
      List.filter_map (fun (b : P.packet) ->
        if b.polarity = P.Borrow && l.sid = b.sid
           && equal_ty l.typ.normalized b.typ.normalized
        then Some (l,b) else None) (roots bd)) (roots ld) in
  match pairs with
  | [pair] -> pair
  | [] -> reject span "no level-zero complementary packet for selected owners"
  | _ -> reject span "ambiguous level-zero complementary packet selection"

(** The ordinary native shared-edge merge removes a right borrow when its
    loan is retained on the left. It does not cancel either owner's symbolic
    projector. Restrict this path to a single unambiguous root edge. *)
let shared_edge span (left : P.descriptor) (right : P.descriptor) =
  let pairs (loan_owner : abs) (borrow_owner : abs) =
    List.concat_map (fun (loan : tavalue) -> match loan.value with
      | ALoan (ASharedLoan (PNone, bid, _, _)) ->
          List.filter_map (fun (borrow : tavalue) -> match borrow.value with
            | ABorrow (ASharedBorrow (PNone, bid', sid)) when bid = bid' ->
                Some (loan, borrow, bid, sid)
            | _ -> None) borrow_owner.avalues
      | _ -> []) loan_owner.avalues
  in
  match pairs left.owner right.owner with
  | [] -> None
  | [edge] ->
      require span (pairs right.owner left.owner = [])
        "concrete shared merge has a reverse internal edge";
      let symbolic_pair a b = List.exists (fun (loan : P.packet) ->
        loan.polarity = P.Loan && List.exists (fun (borrow : P.packet) ->
          borrow.polarity = P.Borrow && loan.sid = borrow.sid
          && equal_ty loan.typ.normalized borrow.typ.normalized) (roots b)) (roots a) in
      require span (not (symbolic_pair left right || symbolic_pair right left))
        "concrete shared merge also requires symbolic cancellation";
      Some edge
  | _ -> reject span "ambiguous concrete shared merge edges"

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
