open Values
open Types
open Contexts
open Utils
open TypesUtils
open ValuesUtils
open InterpUtils
open InterpBorrowsCore
open InterpAbs
open InterpJoinCore
open InterpMatchCtxs

(** The local logger *)
let log = Logging.reduce_collapse_log

(** Attempts to eliminate useless shared loans, in particular to get rid of
    remaining markers.

    We simply eliminate shared loans which don't have corresponding shared
    borrows.

    TODO: will not be necessary once we destructure the avalues. *)
let eliminate_shared_loans (span : Meta.span) (ctx : eval_ctx) : eval_ctx =
  (* Compute the set of shared borrows *)
  let ids, _ = compute_ctx_ids ctx in
  let shared_borrows = ids.non_unique_shared_borrow_ids in

  let update_loans =
    object (self)
      inherit [_] map_abs as super

      method! visit_ASharedLoan env pm bid sv child =
        if
          (not (BorrowId.Set.mem bid shared_borrows))
          &&
          (* We have to pay attention to markers: if there is a borrow/loan
              inside the shared value, by removing the shared loan we forget
              about the marker, which can be a problem *)
          not (value_has_loans_or_borrows (Some span) ctx sv.value)
        then self#visit_AEndedSharedLoan env sv child
        else super#visit_ASharedLoan env pm bid sv child
    end
  in
  let update_abs (abs : abs) : abs =
    (* Only update the non-frozen abstractions *)
    if abs.can_end then update_loans#visit_abs () abs else abs
  in
  let ctx = ctx_map_abs update_abs ctx in

  (* Remove the ended shared loans, if possible *)
  let ctx = InterpBorrows.eliminate_ended_shared_loans span ctx in

  (* *)
  ctx

(** Compute the set of shared loans and shared loan projectors without markers
    appearing in the context *)
let get_non_marked_shared_loans _span (ctx : eval_ctx) :
    BorrowId.Set.t * NormSymbProj.Set.t =
  let non_marked_loans = ref BorrowId.Set.empty in
  let non_marked_projs = ref NormSymbProj.Set.empty in
  let collect_loans =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_ASharedLoan env pm lid sv child =
        if pm = PNone then
          non_marked_loans := BorrowId.Set.add lid !non_marked_loans;
        super#visit_ASharedLoan env pm lid sv child

      method! visit_VSharedLoan env lid sv =
        non_marked_loans := BorrowId.Set.add lid !non_marked_loans;
        super#visit_VSharedLoan env lid sv

      method! visit_ASymbolic env pm aproj =
        match aproj with
        | AProjLoans { proj; consumed = []; borrows = [] } ->
            (* This set authorizes introducing a shared borrow in the other
               branch. Only a complete history-free root supplies that key.
               Marked roots are not shared across both branches. *)
            if pm = PNone then (
              let pred (r : region) =
                match r with
                | RVar (Free rid) -> RegionId.Set.mem rid env
                | _ -> false
              in
              if
                not
                  (ty_has_mut_borrow_for_region_in_pred ctx.type_ctx.type_infos
                     pred proj.proj_ty)
              then (
                let proj = normalize_symbolic_proj env proj in
                non_marked_projs := NormSymbProj.Set.add proj !non_marked_projs;
                super#visit_ASymbolic env pm aproj))
        | AProjLoans _ ->
            (* A consumed part or an ancestor-return history is not evidence
               that the root's complete mask can be copied. Keep the entire
               original projector/history in the context; neither it nor its
               historical descendants authorize new borrows here. Native
               ending and the final marker checks still handle those roots. *)
            ()
        | _ -> super#visit_ASymbolic env pm aproj

      method! visit_abs _ abs = super#visit_abs abs.regions.owned abs
    end
  in
  collect_loans#visit_eval_ctx RegionId.Set.empty ctx;
  (!non_marked_loans, !non_marked_projs)

type borrow_or_proj =
  | Borrow of borrow_id
  | Proj of RegionId.Set.t * symbolic_proj

(** Attempts to eliminate remaining markers over shared borrows.

    We can eliminate a marker over a shared borrow if the corresponding loan in
    the context doesn't have markers. The reason is that we are always allowed
    to introduce a shared borrow for an existing shared loan: in order to remove
    the marker, we can introduce a shared borrow in the other environment.

    For instance, the following is legal:
    {[
      x -> SL l v
      abs { |SB l| } // the left environment has a borrow, but not the right one

        ~>

      x -> SL l v
      abs { SB l } // introduce SB l in the right environment and add it to the abstraction
    ]}

    Note that we do the same for symbolic values: if a symbolic projection only
    projects shared borrows and there exists the corresponding loan projector,
    then we eliminate the marker. *)
let eliminate_shared_borrow_markers (span : Meta.span)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_or_proj * ty) list ref option)
    (ctx : eval_ctx) : eval_ctx =
  (* Compute the set of loans without markers *)
  let non_marked_loans, non_marked_loan_projs =
    get_non_marked_shared_loans span ctx
  in
  [%ldebug
    "- non_marked_loans: "
    ^ BorrowId.Set.to_string None non_marked_loans
    ^ "\n- non_marked_loan_projs: "
    ^ NormSymbProj.Set.with_ctx_to_string None ctx non_marked_loan_projs];

  match shared_borrows_seq with
  | None ->
      let update_borrows =
        object
          inherit [_] map_eval_ctx as super

          method! visit_ASharedBorrow env pm bid sid =
            let pm =
              if BorrowId.Set.mem bid non_marked_loans then PNone else pm
            in
            super#visit_ASharedBorrow env pm bid sid

          method! visit_ASymbolic regions pm aproj =
            match aproj with
            | AProjBorrows { proj; loans = [] } ->
                let pm =
                  let nproj = normalize_symbolic_proj regions proj in
                  if
                    pm <> PNone
                    && NormSymbProj.Set.mem nproj non_marked_loan_projs
                  then PNone
                  else pm
                in
                super#visit_ASymbolic regions pm
                  (AProjBorrows { proj; loans = [] })
            | _ -> super#visit_ASymbolic regions pm aproj

          method! visit_abs _ abs = super#visit_abs abs.regions.owned abs
        end
      in
      update_borrows#visit_eval_ctx RegionId.Set.empty ctx
  | Some shared_borrows ->
      (* We need to register the borrows out of which we eliminate the markers.
         For now, we can't register the addition of shared borrows at arbitrary
         positions. TODO: generalize. *)
      let update_avalue (regions : RegionId.Set.t) (offset : int ref)
          (aid : abs_id) (i : int) (av : tavalue) : tavalue =
        match av.value with
        | ABorrow (ASharedBorrow (pm, bid, sid)) ->
            let pm =
              if pm <> PNone && BorrowId.Set.mem bid non_marked_loans then (
                (* Register the fact that we need to introduce a new shared borrow *)
                let pm' =
                  match pm with
                  | PNone -> [%internal_error] span
                  | PLeft -> PRight
                  | PRight -> PLeft
                in
                let _, ty, _ = ty_get_ref av.ty in
                shared_borrows :=
                  (aid, i + !offset, pm', Borrow bid, ty) :: !shared_borrows;
                offset := !offset + 1;
                PNone)
              else pm
            in
            { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
        | ASymbolic (pm, AProjBorrows { proj; loans = [] }) ->
            [%ldebug "Found symbolic borrow proj:\n" ^ tavalue_to_string ctx av];
            let pm =
              let nproj = normalize_symbolic_proj regions proj in
              if pm <> PNone && NormSymbProj.Set.mem nproj non_marked_loan_projs
              then (
                (* Register the fact that we need to introduce a new shared borrow *)
                let pm' =
                  match pm with
                  | PNone -> [%internal_error] span
                  | PLeft -> PRight
                  | PRight -> PLeft
                in
                let _, ty, _ = ty_get_ref av.ty in
                shared_borrows :=
                  (aid, i + !offset, pm', Proj (regions, proj), ty)
                  :: !shared_borrows;
                offset := !offset + 1;
                PNone)
              else pm
            in
            {
              av with
              value = ASymbolic (pm, AProjBorrows { proj; loans = [] });
            }
        | _ -> av
      in
      let update_borrows =
        object
          inherit [_] map_eval_ctx

          method! visit_abs regions abs =
            {
              abs with
              avalues =
                List.mapi (update_avalue regions (ref 0) abs.abs_id) abs.avalues;
            }
        end
      in
      update_borrows#visit_eval_ctx RegionId.Set.empty ctx

(** Eliminate the markers of ended loans/borrows

    TODO: the projection markers should be placed in aproj/eproj rather than
    ASymbolic/ESymbolic *)
let eliminate_ended_markers (_span : Meta.span) (ctx : eval_ctx) : eval_ctx =
  (* We also remove the markers from the ended loans/borrows in the evalues *)
  let update_abs (abs : abs) : abs =
    let visitor =
      object
        inherit [_] map_abs as super

        method! visit_ESymbolic env pm proj =
          match proj with
          | EEndedProjLoans { proj_ty = _; proj = _; consumed; borrows }
            when List.for_all
                   (fun (_, proj) -> proj = EEmpty)
                   (consumed @ borrows) -> super#visit_ESymbolic env PNone proj
          | EEndedProjBorrows { proj_ty = _; mvalues = _; loans }
            when List.for_all (fun (_, proj) -> proj = EEmpty) loans ->
              super#visit_ESymbolic env PNone proj
          | _ -> super#visit_ESymbolic env pm proj
      end
    in
    let cont = Option.map (visitor#visit_abs_cont ()) abs.cont in

    (* *)
    { abs with cont }
  in
  let ctx = ctx_map_abs update_abs ctx in

  (* *)
  ctx

(** Utility.

    An environment augmented with information about its
    borrows/loans/abstractions for the purpose of merging abstractions together.
    We provide functions to update this information when merging two
    abstractions together. We use it in {!reduce_ctx} and {!collapse_ctx}. *)
type ctx_with_info = { ctx : eval_ctx; info : abs_borrows_loans_maps }

let ctx_with_info_merge_into_first_abs (span : Meta.span) (abs_kind : abs_kind)
    ~(fixed_abs_ids : AbsId.Set.t) ~(can_end : bool) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : ctx_with_info)
    (abs_id0 : AbsId.id) (abs_id1 : AbsId.id) : ctx_with_info * abs_id =
  [%ldebug
    "Merging abstraction " ^ AbsId.to_string abs_id1 ^ " into abstraction "
    ^ AbsId.to_string abs_id0];
  (* Compute the new context and the new abstraction id *)
  let nctx, nabs_id =
    merge_into_first_abstraction ~packet_fixed_abs_ids:fixed_abs_ids
      span abs_kind ~can_end ~with_abs_conts merge_funs ctx.ctx abs_id0 abs_id1
  in
  let nabs = ctx_lookup_abs nctx nabs_id in
  if InterpPacketRouting.enabled () && InterpPacketRouting.requires_merge nabs then (
    (* Rebuild from the actual new environment, not a singleton with stale ctx.
       This indexes only roots and revalidates all retained packet histories. *)
    let info = compute_abs_borrows_loans_maps span
      (fun a -> not (AbsId.Set.mem a.abs_id fixed_abs_ids)) nctx nctx.env in
    ({ctx=nctx;info},nabs_id))
  else begin
  [%ldebug
    "abstraction resulting from the merge:\n" ^ abs_to_string span ctx.ctx nabs];
  (* Update the information *)
  (* We start by computing the maps for an environment which only contains
     the new region abstraction *)
  let {
    abs_to_borrows = nabs_to_borrows;
    abs_to_non_unique_borrows = nabs_to_non_unique_borrows;
    abs_to_loans = nabs_to_loans;
    borrow_to_abs = borrow_to_nabs;
    non_unique_borrow_to_abs = non_unique_borrow_to_nabs;
    loan_to_abs = loan_to_nabs;
    abs_to_borrow_projs = nabs_to_borrow_projs;
    abs_to_loan_projs = nabs_to_loan_projs;
    borrow_proj_to_abs = borrow_proj_to_nabs;
    loan_proj_to_abs = loan_proj_to_nabs;
    _;
  } =
    compute_abs_borrows_loans_maps span (fun _ -> true) ctx.ctx [ EAbs nabs ]
  in
  (* Retrieve the previous maps, so that we can update them *)
  let {
    abs_ids;
    abs_to_borrows;
    abs_to_non_unique_borrows;
    abs_to_loans;
    borrow_to_abs;
    non_unique_borrow_to_abs;
    loan_to_abs;
    abs_to_borrow_projs;
    abs_to_loan_projs;
    borrow_proj_to_abs;
    loan_proj_to_abs;
  } =
    ctx.info
  in
  let abs_ids =
    List.filter_map
      (fun id ->
        if id = abs_id0 then Some nabs_id
        else if id = abs_id1 then None
        else Some id)
      abs_ids
  in
  (* Update the various maps.

     We use a functor for the maps from marked borrows/loans or symbolic value
     projections to symbolic abstractions, because we have to manipulate maps and
     sets over different types (borrow/loan ids and symbolic value projections).
  *)
  let module UpdateToAbs
      (M : Collections.Map)
      (S : Collections.Set with type elt = M.key) =
  struct
    (* Update a map from marked borrows/loans or symbolic value projections
       to region abstractions by using the old map and the information computed
       from the merged abstraction. *)
    let update_to_abs ~(to_abs_inj : bool) (key_to_string : M.key -> string)
        (abs_to : S.t AbsId.Map.t) (to_nabs : AbsId.Set.t M.t)
        (to_abs : AbsId.Set.t M.t) : AbsId.Set.t M.t =
      (* Remove the old bindings from borrow/loan ids to the two region
         abstractions we just merged (because those two region abstractions
         do not exist anymore). *)
      let abs0_elems = AbsId.Map.find abs_id0 abs_to in
      let abs1_elems = AbsId.Map.find abs_id1 abs_to in
      let abs01_elems = S.union abs0_elems abs1_elems in
      (* Remove the to_abs mapping if to_abs is injective *)
      let to_abs =
        if to_abs_inj then
          M.filter (fun id _ -> not (S.mem id abs01_elems)) to_abs
        else to_abs
      in
      (* Add the new bindings from the borrows/loan ids that we find in the
         merged abstraction to this abstraction's id *)
      let merge (key : M.key) (abs0 : AbsId.Set.t) (abs1 : AbsId.Set.t) =
        (* We shouldn't see the same key twice if the [to_abs] map is injective *)
        if to_abs_inj then
          [%craise] span
            ("Unreachable:\n key: " ^ key_to_string key ^ "\n- abs0: "
            ^ AbsId.Set.to_string None abs0
            ^ "\n- abs1: "
            ^ AbsId.Set.to_string None abs1)
        else Some (AbsId.Set.union abs0 abs1)
      in
      let to_abs = M.union merge to_nabs to_abs in
      (* Filter to remove the old abstraction ids *)
      M.filter_map
        (fun _ s ->
          let s =
            AbsId.Set.filter
              (fun (id : abs_id) -> id <> abs_id0 && id <> abs_id1)
              s
          in
          if AbsId.Set.is_empty s then None else Some s)
        to_abs
  end in
  let module UpdateMarkedBorrowId =
    UpdateToAbs (MarkedBorrowId.Map) (MarkedBorrowId.Set)
  in
  let module UpdateMarkedUniqueBorrowId =
    UpdateToAbs (MarkedUniqueBorrowId.Map) (MarkedUniqueBorrowId.Set)
  in
  let module UpdateMarkedLoanId =
    UpdateToAbs (MarkedLoanId.Map) (MarkedLoanId.Set)
  in
  let marked_unique_borrow_id_to_string
      ((pm, bid, sid) : marked_unique_borrow_id) : string =
    let s =
      match sid with
      | None -> "MB@" ^ show_borrow_id bid
      | Some sid ->
          "SB@" ^ show_borrow_id bid ^ "(^" ^ show_shared_borrow_id sid ^ ")"
    in
    Print.Values.add_proj_marker pm s
  in
  let borrow_to_abs =
    UpdateMarkedUniqueBorrowId.update_to_abs ~to_abs_inj:true
      marked_unique_borrow_id_to_string abs_to_borrows borrow_to_nabs
      borrow_to_abs
  in
  let non_unique_borrow_to_abs =
    UpdateMarkedBorrowId.update_to_abs ~to_abs_inj:false show_marked_borrow_id
      abs_to_non_unique_borrows non_unique_borrow_to_nabs
      non_unique_borrow_to_abs
  in
  let loan_to_abs =
    UpdateMarkedLoanId.update_to_abs ~to_abs_inj:true show_marked_borrow_id
      abs_to_loans loan_to_nabs loan_to_abs
  in
  let module UpdateSymbProj =
    UpdateToAbs (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
  in
  let borrow_proj_to_abs =
    UpdateSymbProj.update_to_abs ~to_abs_inj:false show_marked_norm_symb_proj
      abs_to_borrow_projs borrow_proj_to_nabs borrow_proj_to_abs
  in
  let loan_proj_to_abs =
    UpdateSymbProj.update_to_abs ~to_abs_inj:false show_marked_norm_symb_proj
      abs_to_loan_projs loan_proj_to_nabs loan_proj_to_abs
  in

  (* Update the maps from abstractions to marked borrows/loans or
     symbolic value projections.
  *)
  let update_abs_to nabs_to abs_to =
    (* Remove the two region abstractions we merged *)
    let m = AbsId.Map.remove abs_id0 (AbsId.Map.remove abs_id1 abs_to) in
    (* Add the merged abstraction *)
    AbsId.Map.add_strict nabs_id (AbsId.Map.find nabs_id nabs_to) m
  in
  let abs_to_borrows = update_abs_to nabs_to_borrows abs_to_borrows in
  let abs_to_non_unique_borrows =
    update_abs_to nabs_to_non_unique_borrows abs_to_non_unique_borrows
  in
  let abs_to_loans = update_abs_to nabs_to_loans abs_to_loans in
  let abs_to_borrow_projs =
    update_abs_to nabs_to_borrow_projs abs_to_borrow_projs
  in
  let abs_to_loan_projs = update_abs_to nabs_to_loan_projs abs_to_loan_projs in
  let info =
    {
      abs_ids;
      abs_to_borrows;
      abs_to_non_unique_borrows;
      abs_to_loans;
      borrow_to_abs;
      non_unique_borrow_to_abs;
      loan_to_abs;
      borrow_proj_to_abs;
      loan_proj_to_abs;
      abs_to_borrow_projs;
      abs_to_loan_projs;
    }
  in
  ({ ctx = nctx; info }, nabs_id)
  end

exception AbsToMerge of abs_id * abs_id

(** Repeatedly iterate through the borrows/loans in an environment and merge the
    abstractions that have to be merged according to a user-provided policy.

    [sequence]: we save the sequence of merges there, in reverse order (the last
    merges are pushed at the front). *)
let repeat_iter_borrows_merge ?recorded_packet_merges (span : Meta.span) (fixed_abs_ids : AbsId.Set.t)
    (abs_kind : abs_kind) ~(can_end : bool) ~(with_abs_conts : bool)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (merge_funs : merge_duplicates_funcs option)
    (iter : ctx_with_info -> ('a -> unit) -> unit)
    (policy : ctx_with_info -> 'a -> (abs_id * abs_id) option) (ctx : eval_ctx)
    : eval_ctx =
  (* Compute the information *)
  let to_ctx_with_info (ctx : eval_ctx) : ctx_with_info =
    let is_fresh_abs_id (id : AbsId.id) : bool =
      not (AbsId.Set.mem id fixed_abs_ids)
    in
    let explore (abs : abs) = is_fresh_abs_id abs.abs_id in
    let info = compute_abs_borrows_loans_maps span explore ctx ctx.env in
    { ctx; info }
  in
  let ctx = to_ctx_with_info ctx in
  (* Explore and merge *)
  let rec explore_merge (ctx : ctx_with_info) : eval_ctx =
    let ctx0 = ctx in
    try
      iter ctx (fun x ->
          (* Check if we need to merge some abstractions *)
          match policy ctx x with
          | None -> (* No *) ()
          | Some (abs_id0, abs_id1) ->
              (* Yes: raise an exception *)
              raise (AbsToMerge (abs_id0, abs_id1)));
      (* No exception raise: return the current context *)
      ctx.ctx
    with AbsToMerge (abs_id0, abs_id1) ->
      let packet_action =
        if InterpPacketRouting.enabled () && Option.is_some sequence
           && (InterpPacketRouting.requires_merge (ctx_lookup_abs ctx.ctx abs_id0)
               || InterpPacketRouting.requires_merge (ctx_lookup_abs ctx.ctx abs_id1)) then begin
          InterpPacketRouting.require span
            (with_abs_conts && Option.is_some merge_funs && Option.is_some recorded_packet_merges)
            "packet merge recording requires the typed right-projection companion";
          try Some (InterpPacketRouting.record_merge span ctx.ctx
            ~fixed_aids:fixed_abs_ids (ctx_lookup_abs ctx.ctx abs_id0) (ctx_lookup_abs ctx.ctx abs_id1))
          with error ->
            let backtrace=Printexc.get_raw_backtrace () in
            Printf.eprintf "RECORDED_PACKET_SELECTION_REJECTED left=%s right=%s\n%s\n%s\n%!"
              (AbsId.to_string abs_id0) (AbsId.to_string abs_id1)
              (abs_to_string span ~with_ended:true ctx.ctx (ctx_lookup_abs ctx.ctx abs_id0))
              (abs_to_string span ~with_ended:true ctx.ctx (ctx_lookup_abs ctx.ctx abs_id1));
            Printexc.raise_with_backtrace error backtrace
        end else None in
      (* Merge and recurse *)
      let ctx, naid =
        ctx_with_info_merge_into_first_abs span abs_kind ~fixed_abs_ids ~can_end
          ~with_abs_conts merge_funs ctx abs_id0 abs_id1
      in
      (* Sanity check: the information was properly updated *)
      if !Config.sanity_checks then
        (let info = ctx.info in
         let info' = (to_ctx_with_info ctx.ctx).info in

         let print_msg (field : string) =
           [%ltrace
             "Invalid incremental update of the context information: field '"
             ^ field ^ "':" ^ "\n- incremental computation:\n"
             ^ abs_borrows_loans_maps_to_string ctx.ctx info
             ^ "\n\n- reference computation:\n"
             ^ abs_borrows_loans_maps_to_string ctx.ctx info'
             ^ "\n\n- initial context:\n"
             ^ eval_ctx_to_string ctx0.ctx
             ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx.ctx];
           [%internal_error] span
         in
         let check (b : bool) (field : string) =
           if not b then print_msg field
         in
         check (info.abs_ids = info'.abs_ids) "abs_ids";
         check
           (AbsId.Map.equal MarkedUniqueBorrowId.Set.equal info.abs_to_borrows
              info'.abs_to_borrows)
           "abs_to_borrows";
         check
           (AbsId.Map.equal MarkedBorrowId.Set.equal
              info.abs_to_non_unique_borrows info'.abs_to_non_unique_borrows)
           "abs_to_non_unique_borrows";
         check
           (AbsId.Map.equal MarkedLoanId.Set.equal info.abs_to_loans
              info'.abs_to_loans)
           "abs_to_loans";
         check
           (MarkedUniqueBorrowId.Map.equal AbsId.Set.equal info.borrow_to_abs
              info'.borrow_to_abs)
           "borrow_to_abs";
         check
           (MarkedBorrowId.Map.equal AbsId.Set.equal
              info.non_unique_borrow_to_abs info'.non_unique_borrow_to_abs)
           "non_unique_borrow_to_abs";
         check
           (MarkedLoanId.Map.equal AbsId.Set.equal info.loan_to_abs
              info'.loan_to_abs)
           "loan_to_abs";
         check
           (AbsId.Map.equal MarkedNormSymbProj.Set.equal
              info.abs_to_borrow_projs info'.abs_to_borrow_projs)
           "abs_to_borrow_projs";
         check
           (AbsId.Map.equal MarkedNormSymbProj.Set.equal info.abs_to_loan_projs
              info'.abs_to_loan_projs)
           "abs_to_loan_projs";
         check
           (MarkedNormSymbProj.Map.equal AbsId.Set.equal info.borrow_proj_to_abs
              info'.borrow_proj_to_abs)
           "borrow_proj_to_abs";
         check
           (MarkedNormSymbProj.Map.equal AbsId.Set.equal info.loan_proj_to_abs
              info'.loan_proj_to_abs))
          "loan_proj_to_abs";
      (* Publish the typed action only after the real merge and all checks pass. *)
      Option.iter (fun action ->
        let actions=Option.get recorded_packet_merges in
        actions := (naid,action) :: !actions) packet_action;
      (* Remember the sequence of merges *)
      Option.iter
        (fun sequence -> sequence := (abs_id0, abs_id1, naid) :: !sequence)
        sequence;
      explore_merge ctx
  in
  explore_merge ctx

let convert_fresh_dummy_values_to_abstractions (span : Meta.span)
    (fresh_abs_kind : abs_kind) (fixed_dids : DummyVarId.Set.t)
    (ctx0 : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx0
    ^ "\n\n- fixed_dids: "
    ^ DummyVarId.Set.to_string None fixed_dids];

  let can_end = true in
  let is_fresh_did (id : DummyVarId.id) : bool =
    not (DummyVarId.Set.mem id fixed_dids)
  in

  let ctx = ctx0 in
  (* Convert the dummy values to abstractions (note that when we convert
     values to abstractions, the resulting abstraction should be destructured) *)
  (* Note that we preserve the order of the dummy values: we replace them with
     abstractions in place - this makes matching easier *)
  let env =
    List.concat
      (List.map
         (fun ee ->
           match ee with
           | EAbs _ | EFrame | EBinding (BVar _, _) -> [ ee ]
           | EBinding (BDummy id, v) ->
               if is_fresh_did id then (
                 let absl =
                   convert_value_to_abstractions span fresh_abs_kind ~can_end
                     ctx v
                 in
                 Invariants.opt_type_check_absl span ctx absl;
                 List.map (fun abs -> EAbs abs) absl)
               else [ ee ])
         ctx.env)
  in
  let ctx = { ctx with env } in
  [%ltrace
    "after converting values to abstractions:" ^ "\n- ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  ctx

(** Reduce an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point (this is our equivalent of Abstract Interpretation's
    **widening** operation).

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not) and convert them into abstractions. TODO: we
      don't do this anymore
    - whenever there is a new abstraction in the context, and some of its
      borrows are associated to loans in another new abstraction, we merge them.
      We also do this with loan/borrow projectors over symbolic values. In
      effect, this allows us to merge newly introduced abstractions/borrows with
      their parent abstractions.

    For instance, looking at the [list_nth_mut] example, when evaluating the
    first loop iteration, we start in the following environment:
    {[
      abs@0 { ML l0 }
      ls -> MB l0 (s2 : loops::List<T>)
      i -> s1 : u32
    ]}

    and get the following environment upon reaching the [Continue] statement:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
      _@2 -> MB l2 (@Box (ML l4))                      // tail
      _@3 -> MB l1 (s@3 : T)                           // hd
    ]}

    In this new environment, the dummy variables [_@1], [_@2] and [_@3] are
    considered as new.

    We first convert the new dummy values to abstractions. It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@1 { MB l0, ML l1, ML l2 }
      abs@2 { MB l2, ML l4 }
      abs@3 { MB l1 }
    ]}

    We finally merge the new abstractions together (abs@1 and abs@2 because of
    l2, and abs@1 and abs@3 because of l1). It gives:
    {[
      abs@0 { ML l0 }
      ls -> MB l4 (s@6 : loops::List<T>)
      i -> s@7 : u32
      abs@4 { MB l0, ML l4 }
    ]}

    - If [merge_funs] is [None], we check that there are no markers in the
      environments. This is the "reduce" operation.
    - If [merge_funs] is [Some _], when merging abstractions together, we merge
      the pairs of borrows and the pairs of loans with the same markers **if
      this marker is not** [PNone]. This is useful to reuse the reduce operation
      to implement the collapse. Note that we ignore borrows/loans with the
      [PNone] marker: the goal of the collapse operation is to *eliminate*
      markers, not to simplify the environment.

    For instance, when merging:
    {[
      abs@0 { ML l0, |MB l1| }
      abs@1 { MB l0, ︙MB l1︙ }
    ]}
    We get:
    {[
      abs@2 { MB l1 }
    ]} *)
let reduce_ctx_with_markers ?config ?recorded_packet_merges (merge_funs : merge_duplicates_funcs option)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    ~(with_abs_conts : bool) (span : Meta.span) (fresh_abs_kind : abs_kind)
    (fixed_abs_ids : AbsId.Set.t) ?(fixed_dids : DummyVarId.Set.t option = None)
    (ctx0 : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace "- ctx0:\n" ^ eval_ctx_to_string ~span:(Some span) ctx0];

  let with_markers = merge_funs <> None in
  let can_end = true in

  let ctx = ctx0 in
  (* Convert the fresh dummy values to abstractions, if the caller requests so
     (note that when we convert values to abstractions, the resulting abstraction
     should be destructured) *)
  let ctx =
    match fixed_dids with
    | None -> ctx
    | Some fixed_dids ->
        convert_fresh_dummy_values_to_abstractions span fresh_abs_kind
          fixed_dids ctx
  in

  (* An identity reborrow can have live native parent-return subscribers.
     Return it through the normal borrow machinery before contraction would
     remove their parent permission. Synthesis/recorded/marked reductions keep
     their existing path; the helper also preserves the original fixed owners. *)
  let ctx =
    match config, merge_funs, sequence with
    | Some config, None, None when not with_abs_conts ->
        InterpAbs.end_subscribed_identity_reborrows config span fixed_abs_ids ctx0 ctx
    | _ -> ctx
  in

  (*
   * Merge all the mergeable abs.
   *)
  (* Because we need to manipulate different types for the concrete and the
     symbolic loans and borrows, we introduce a functor *)
  let module IterMerge
      (Map : Collections.Map)
      (Set : Collections.Set with type elt = Map.key)
      (Marked : sig
        val get_marker : Map.key -> proj_marker
        val get_borrow_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
        val get_to_loans : abs_borrows_loans_maps -> Set.t AbsId.Map.t
        val retained_self_edge : ctx_with_info -> AbsId.id -> Map.key -> bool
        val retained_payload_edge : ctx_with_info -> AbsId.id -> AbsId.id -> Map.key -> bool
      end) =
  struct
    (* We iterate over the *new* abstractions, then over the **loans**
       (concrete or symbolic) in the abstractions.

       We do this because we want to control the order in which abstractions
       are merged (the ids are iterated in increasing order). Otherwise, we
       could simply iterate over all the borrows in [loan_to_abs] for instance... *)
    let iterate_loans (ctx : ctx_with_info) (merge : abs_id * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Iterate over the loans *)
          let lids = AbsId.Map.find abs_id0 (Marked.get_to_loans ctx.info) in
          Set.iter (fun lid -> merge (abs_id0, lid)) lids)
        ctx.info.abs_ids

    (* Given a **loan**, check if there is a fresh abstraction with the corresponding borrow *)
    let merge_policy (ctx : ctx_with_info) (abs_id0, loan) =
      if not with_markers then
        [%sanity_check] span (Marked.get_marker loan = PNone);
      (* If we use markers: we are doing a collapse, which means we attempt
         to eliminate markers (and this is the only goal of the operation).
         We thus ignore the non-marked values (we merge non-marked values
         when doing a "real" reduce, to simplify the environment in order
         to converge to a fixed-point, for instance). *)
      if with_markers && Marked.get_marker loan = PNone then None
      else
        (* Find the *borrow* corresponding to the loan we want to eliminate
           (hence the use of [get_borrow_to_abs]) *)
        match Map.find_opt loan (Marked.get_borrow_to_abs ctx.info) with
        | None -> (* Nothing to to *) None
        | Some abs_ids1 -> (
            (* Do not flatten a retained cross-level relation by self-merging.
               Its permissions stay fully indexed and native subabs ending is
               still responsible for them. Other borrower owners remain eligible. *)
            let abs_ids1 =
              if AbsId.Set.mem abs_id0 abs_ids1
                 && Marked.retained_self_edge ctx abs_id0 loan then
                AbsId.Set.remove abs_id0 abs_ids1
              else abs_ids1 in
            let abs_ids1 = AbsId.Set.filter (fun borrower ->
              not (Marked.retained_payload_edge ctx abs_id0 borrower loan)) abs_ids1 in
            match AbsId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                [%ltrace
                  "merging abstraction " ^ AbsId.to_string abs_id1 ^ " into "
                  ^ AbsId.to_string abs_id0 ^ ":" ^ "\n- abs "
                  ^ AbsId.to_string abs_id1 ^ ":\n"
                  ^ abs_to_string span ctx.ctx (ctx_lookup_abs ctx.ctx abs_id1)
                  ^ "\n\n- abs " ^ AbsId.to_string abs_id0 ^ ":\n"
                  ^ abs_to_string span ctx.ctx (ctx_lookup_abs ctx.ctx abs_id0)
                  ^ "\n\n"
                  ^ eval_ctx_to_string ~span:(Some span) ctx.ctx];
                Some (abs_id0, abs_id1))

    (* Iterate over the loans and merge the abstractions *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge ?recorded_packet_merges span fixed_abs_ids fresh_abs_kind ~can_end
        ~with_abs_conts sequence merge_funs iterate_loans merge_policy ctx
  end in
  (* Instantiate the functor for the concrete borrows and loans *)
  let module IterMergeConcrete =
    IterMerge (MarkedBorrowId.Map) (MarkedBorrowId.Set)
      (struct
        let get_marker (pm, _) = pm
        let get_borrow_to_abs info = info.non_unique_borrow_to_abs
        let get_to_loans info = info.abs_to_loans
        let retained_self_edge ctx aid loan =
          retained_cross_level_shared_self_edge span ctx.ctx aid loan
        let retained_payload_edge ctx loan_aid borrow_aid (marker,bid) =
          if not (InterpSharedPacketSignature.enabled ()) || loan_aid=borrow_aid then false
          else
            let loan_owner=ctx_lookup_abs ctx.ctx loan_aid
            and borrow_owner=ctx_lookup_abs ctx.ctx borrow_aid in
            (* Shared payload dependencies remain current even after native
               ending removes a parent edge. Only a top-level abstract borrow
               is cancellable by the ordinary flat merge below. *)
              let rec current_fields (value:tavalue) = match value.value with
                | AAdt adt -> List.concat_map current_fields adt.fields
                | ALoan(AIgnoredSharedLoan child) -> current_fields child
                | _ -> [value] in
              let loan_values=List.concat_map current_fields loan_owner.avalues
              and borrow_values=List.concat_map current_fields borrow_owner.avalues in
              let loans=List.filter (fun (value:tavalue) -> match value.value with
                | ALoan(ASharedLoan(pm,id,_,_)) -> pm=marker && id=bid
                | _ -> false) loan_values in
              let payloads=List.filter_map (fun (value:tavalue) -> match value.value with
                | ALoan(ASharedLoan(pm,_,{value=VBorrow(VSharedBorrow(id,sid));_},child))
                  when pm=marker && id=bid -> Some(value,child,sid)
                | _ -> None) borrow_values in
              match loans,payloads with
              | [loan],[(payload,child,sid)]
                when equal_ty loan.ty child.ty ->
                  let indexed=MarkedUniqueBorrowId.Set.filter (fun (pm,id,_) ->
                    pm=marker && id=bid)
                    (AbsId.Map.find borrow_aid ctx.info.abs_to_borrows) in
                  if not (MarkedUniqueBorrowId.Set.equal indexed
                    (MarkedUniqueBorrowId.Set.singleton(marker,bid,Some sid))) then false
                  else begin
                    InterpSharedPacketSignature.check_retained_shared_loan
                      ~allow_marked:true span ctx.ctx loan_owner 0 loan;
                    InterpSharedPacketSignature.check_retained_shared_loan
                      ~allow_marked:true span ctx.ctx borrow_owner 0 payload;
                    (* Keep this nested reference's existing native ownership
                       and parent-return ordering. It is fully indexed, but unlike a top-level
                       ASharedBorrow it cannot be cancelled by ordinary flat
                       merging without discarding the enclosing current loan. *)
                    true
                  end
              | _ -> false
      end)
  in
  (* Instantiate the functor for the symbolic borrows and loans *)
  let module IterMergeSymbolic =
    IterMerge (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
      (struct
        let get_marker (proj : marked_norm_symb_proj) = proj.pm
        let get_borrow_to_abs info = info.borrow_proj_to_abs
        let get_to_loans info = info.abs_to_loan_projs
        let retained_self_edge _ _ _ = false
        let retained_payload_edge _ _ _ _ = false
      end)
  in
  (* Apply *)
  let ctx = IterMergeConcrete.iter_merge ctx in
  let ctx = IterMergeSymbolic.iter_merge ctx in

  (* Debugging *)
  [%ltrace
    "- after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers at this point. *)
  let ctx = reorder_fresh_abs span true fixed_abs_ids ctx in

  [%ltrace
    "- after reduce and reorder borrows/loans and abstractions:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Return the new context *)
  ctx

(** reduce_ctx can only be called in a context with no markers *)
let reduce_ctx config (span : Meta.span)
    ?(sequence : (abs_id * abs_id * abs_id) list ref option = None)
    ~(with_abs_conts : bool) (fresh_abs_kind : abs_kind)
    (fixed_abs_ids : AbsId.Set.t) (fixed_dids : DummyVarId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  (* Simplify the context *)
  let ctx, _ =
    InterpBorrows.simplify_dummy_values_useless_abs config span ctx
  in
  (* Reduce *)
  let ctx =
    reduce_ctx_with_markers ~config None sequence span ~with_abs_conts fresh_abs_kind
      fixed_abs_ids ~fixed_dids:(Some fixed_dids) ctx
  in
  eliminate_shared_loans span ctx

(** Auxiliary function for collapse (see below).

    We traverse all abstractions, and merge abstractions when they contain the
    same element, but with dual markers (i.e., [PLeft] and [PRight]).

    For instance, if we have the abstractions

    {[
      abs@0 { | MB l0 _ |, ML l1 }
      abs@1 { ︙MB l0 _ ︙, ML l2 }
    ]}

    We merge abs@0 and abs@1 into a new abstraction abs@2. This allows us to
    eliminate the markers used for [MB l0]:
    {[
      abs@2 { MB l0 _, ML l1, ML l2 }
    ]} *)
let collapse_ctx_collapse ?recorded_packet_merges (span : Meta.span)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    "\n- initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  let can_end = true in
  let ctx0 = ctx in

  let invert_proj_marker = function
    | PNone -> [%craise] span "Unreachable"
    | PLeft -> PRight
    | PRight -> PLeft
  in

  let fixed_aids = ctx_get_frozen_abs_set ctx in

  (* Merge all the mergeable abs where the same element is present in both abs,
     but with left and right markers respectively.

     As we have to operate over different types, with both concrete borrows and loans and
     borrow projectors and loan projectors, we implement this as a functor.
  *)
  let module IterMerge
      (Map : Collections.Map)
      (Set : Collections.Set with type elt = Map.key)
      (Marked : sig
        val get_marker : Map.key -> proj_marker

        (* Remove a marker - we need this to check whether some borrows in one
           abstraction have corresponding loans in another abstraction,
           independently of the markers, to properly choose which abstraction
           we merge into the other. *)
        val unmark : Map.key -> Map.key

        (* Invert a marker *)
        val invert_proj_marker : Map.key -> Map.key
        val get_to_borrows : abs_borrows_loans_maps -> Set.t AbsId.Map.t
        val get_to_loans : abs_borrows_loans_maps -> Set.t AbsId.Map.t
        val get_borrow_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
        val get_loan_to_abs : abs_borrows_loans_maps -> AbsId.Set.t Map.t
      end) =
  struct
    (* The iter function: iterate over the abstractions, and inside an abstraction
       over the borrows (projectors) then the loan (projectors) *)
    let iter (ctx : ctx_with_info) (f : AbsId.id * bool * Map.key -> unit) =
      List.iter
        (fun abs_id0 ->
          (* Small helper *)
          let iterate is_borrow =
            let m =
              if is_borrow then Marked.get_to_borrows ctx.info
              else Marked.get_to_loans ctx.info
            in
            let ids = AbsId.Map.find abs_id0 m in
            Set.iter (fun id -> f (abs_id0, is_borrow, id)) ids
          in
          (* Iterate over the borrows *)
          iterate true;
          (* Iterate over the loans *)
          iterate false)
        ctx.info.abs_ids

    (* Small utility: check if we need to swap two region abstractions before
       merging them.

       We might have to swap the order to make sure that if there
       are loans in one abstraction and the corresponding borrows
       in the other they get properly merged (if we merge them in the wrong
       order, we might introduce borrowing cycles).

       Example:
       If we are merging abs0 and abs1 because of the marked value
       [MB l0]:
       {[
         abs0 { |MB l0|, MB l1 }
         abs1 { ︙MB l0︙, ML l1 }
       ]}
       we want to make sure that we swap them (abs1 goes to the
       left) to make sure [MB l1] and [ML l1] get properly eliminated.

       Remark: in case there is a borrowing cycle between the two abstractions
       (which shouldn't happen) then there isn't much we can do, and whatever
       the order in which we merge, we will preserve the cycle.
    *)
    let swap_abs (info : abs_borrows_loans_maps) (abs_id0 : abs_id)
        (abs_id1 : abs_id) =
      let abs0_borrows =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements
                (AbsId.Map.find abs_id0 (Marked.get_to_borrows info))))
      in
      let abs1_loans =
        Set.of_list
          (List.map Marked.unmark
             (Set.elements (AbsId.Map.find abs_id1 (Marked.get_to_loans info))))
      in
      not (Set.disjoint abs0_borrows abs1_loans)

    (* Check if there is an abstraction with the same borrow/loan id (or the
       same projections of borrows/loans) and the dual marker, and merge them
       if it is the case. *)
    let merge_policy ctx (abs_id0, is_borrow, loan) =
      if Marked.get_marker loan = PNone then None
      else
        (* Look for an element with the dual marker *)
        match
          Map.find_opt
            (Marked.invert_proj_marker loan)
            (if is_borrow then Marked.get_borrow_to_abs ctx.info
             else Marked.get_loan_to_abs ctx.info)
        with
        | None -> (* Nothing to do *) None
        | Some abs_ids1 -> (
            (* We need to merge *)
            match AbsId.Set.elements abs_ids1 with
            | [] -> None
            | abs_id1 :: _ ->
                (* Check if we need to swap *)
                Some
                  (if swap_abs ctx.info abs_id0 abs_id1 then (abs_id1, abs_id0)
                   else (abs_id0, abs_id1)))

    (* Iterate and merge *)
    let iter_merge (ctx : eval_ctx) : eval_ctx =
      repeat_iter_borrows_merge ?recorded_packet_merges span fixed_aids fresh_abs_kind ~can_end
        ~with_abs_conts sequence (Some merge_funs) iter merge_policy ctx
  end in
  (* Instantiate the functor for concrete loans and borrows *)
  let module IterMergeConcrete =
    IterMerge (MarkedBorrowId.Map) (MarkedBorrowId.Set)
      (struct
        let get_marker (v : marked_borrow_id) = fst v
        let unmark (_, bid) = (PNone, bid)
        let invert_proj_marker (pm, bid) = (invert_proj_marker pm, bid)
        let get_to_borrows info = info.abs_to_non_unique_borrows
        let get_to_loans info = info.abs_to_loans
        let get_borrow_to_abs info = info.non_unique_borrow_to_abs
        let get_loan_to_abs info = info.loan_to_abs
      end)
  in
  (* Instantiate the functor for symbolic loans and borrows *)
  let module IterMergeSymbolic =
    IterMerge (MarkedNormSymbProj.Map) (MarkedNormSymbProj.Set)
      (struct
        let get_marker (v : marked_norm_symb_proj) = v.pm
        let unmark v = { v with pm = PNone }
        let invert_proj_marker v = { v with pm = invert_proj_marker v.pm }
        let get_to_borrows info = info.abs_to_borrow_projs
        let get_to_loans info = info.abs_to_loan_projs
        let get_borrow_to_abs info = info.borrow_proj_to_abs
        let get_loan_to_abs info = info.loan_proj_to_abs
      end)
  in
  (* Iterate and merge *)
  let ctx = IterMergeConcrete.iter_merge ctx in
  let ctx = IterMergeSymbolic.iter_merge ctx in

  [%ltrace
    "- after collapse:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  (* Reorder the fresh region abstractions - note that we may not have eliminated
     all the markers yet *)
  let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
  let ctx = reorder_fresh_abs span true fixed_aids ctx in

  [%ltrace
    "- after collapse and reorder borrows/loans:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n"];

  (* Return the new context *)
  ctx

(** Small utility: check whether an environment contains markers *)
let eval_ctx_has_markers (ctx : eval_ctx) : bool =
  let visitor =
    object
      inherit [_] iter_eval_ctx

      method! visit_proj_marker _ pm =
        match pm with
        | PNone -> ()
        | PLeft | PRight -> raise Found
    end
  in
  try
    visitor#visit_eval_ctx () ctx;
    false
  with Found -> true

(** Collapse two environments containing projection markers; this function is
    called after joining environments.

    The collapse is done in two steps.

    First, we reduce the environment, merging any two pair of fresh abstractions
    which contain a loan (in one) and its corresponding borrow (in the other).
    This is our version of Abstract Interpretation's **widening** operation. For
    instance, we merge abs@0 and abs@1 below:
    {[
      abs@0 { |ML l0|, ML l1 }
      abs@1 { |MB l0 _|, ML l2 }
                ~~>
      abs@2 { ML l1, ML l2 }
    ]}
    Note that we also merge abstractions when the loan/borrow don't have the
    same markers. For instance, below:
    {[
      abs@0 { ML l0, ML l1 } // ML l0 doesn't have markers
      abs@1 { |MB l0 _|, ML l2 }
                ~~>
      abs@2 { ︙ML l0︙, ML l1, ML l2 }
    ]}

    Second, we merge abstractions containing the same element with left and
    right markers respectively. For instance:
    {[
      abs@0 { | MB l0 _ |, ML l1 }
      abs@1 { ︙MB l0 _ ︙, ML l2 }
                ~~>
      abs@2 { MB l0 _, ML l1, ML l2 }
    ]}

    At the end of the second step, all markers should have been removed from the
    resulting environment. *)
(** A strict analysis-only extension of the existing dead-projector ending
    operation. We never end an abstraction, clear arbitrary markers, or change
    IDs/parents. Recorded merge replays and all synthesized continuations retain
    the original path. *)
let end_dead_shared_analysis_projections config (span : Meta.span)
    ~(with_abs_conts : bool) ~(recording : bool)
    (fixed_aids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let trace=Sys.getenv_opt "AENEAS_TRACE_DEAD_SHARED_ANALYSIS_PROJECTIONS"=Some "1" in
  if trace then Printf.eprintf "DEAD_SHARED_ANALYSIS_GATE enabled=%b synthesis=%b recording=%b\n%!"
    (Sys.getenv_opt "AENEAS_EXPERIMENTAL_DEAD_SHARED_ANALYSIS_PROJECTIONS"=Some "1")
    with_abs_conts recording;
  if Sys.getenv_opt "AENEAS_EXPERIMENTAL_DEAD_SHARED_ANALYSIS_PROJECTIONS"
       <> Some "1" || with_abs_conts || recording then ctx
  else
    let used_elsewhere ?(report=false) (ctx : eval_ctx) (target : abs) index sid =
      (* Remove only this current top-level occurrence. Captured environments
         retain the original abstraction and must be scanned independently. *)
      let scan_env = List.map (function
        | EAbs abs when abs.abs_id = target.abs_id ->
            EAbs {abs with avalues = List.filteri (fun i _ -> i <> index) abs.avalues}
        | entry -> entry) ctx.env in
      let seen_envs = ref [] in
      let path=ref [] and references=ref [] in
      let at label f =
        let previous= !path in
        path:=label::previous;
        Fun.protect ~finally:(fun () -> path:=previous) f in
      let visitor = object (self)
        inherit [_] iter_eval_ctx as super
        method! visit_env () env =
          if not (List.exists (fun previous -> previous == env) !seen_envs) then (
            seen_envs := env :: !seen_envs;
            List.iteri (fun i entry -> at ("env/"^string_of_int i)
              (fun () -> self#visit_env_elem () entry)) env)
        method! visit_env_elem () entry =
          let label=match entry with
            | EBinding(binder,_) -> "runtime:"^show_var_binder binder
            | EAbs owner -> "abs@"^AbsId.to_string owner.abs_id
            | EFrame -> "frame" in
          at label (fun () -> super#visit_env_elem () entry)
        method! visit_abs () owner =
          if report then begin
            List.iteri (fun i value -> at ("avalue/"^string_of_int i)
              (fun () -> self#visit_tavalue () value)) owner.avalues;
            Option.iter (fun cont -> at "continuation"
              (fun () -> self#visit_abs_cont () cont)) owner.cont
          end else super#visit_abs () owner
        method! visit_tavalue () value =
          let label=match value.value with
            | ASymbolic(_,AProjLoans _) -> "A/loan"
            | ASymbolic(_,AProjBorrows _) -> "A/borrow"
            | ASymbolic(_,AEndedProjLoans _) -> "A/ended-loan"
            | ASymbolic(_,AEndedProjBorrows _) -> "A/ended-borrow"
            | ALoan(ASharedLoan(_,bid,_,_)) -> "A/shared-loan@"^BorrowId.to_string bid
            | _ -> "A/value" in
          at label (fun () -> super#visit_tavalue () value)
        method! visit_tevalue () value =
          at "E/value" (fun () -> super#visit_tevalue () value)
        method! visit_tvalue () value =
          let label=match value.value with
            | VLoan(VSharedLoan(bid,_)) -> "runtime/shared-loan@"^BorrowId.to_string bid
            | VBorrow(VMutBorrow(bid,_)) -> "runtime/mut-borrow@"^BorrowId.to_string bid
            | VSymbolic _ -> "runtime/symbolic"
            | _ -> "runtime/value" in
          at label (fun () -> super#visit_tvalue () value)
        method! visit_symbolic_value_id () id =
          if id=sid then
            if report then references:=String.concat "/" (List.rev !path):: !references
            else raise Found
        method! visit_mvalue () value =
          at "metadata/value" (fun () -> self#visit_tvalue () value)
        method! visit_msymbolic_value () value =
          at "metadata/symbolic" (fun () -> self#visit_symbolic_value () value)
        method! visit_msymbolic_value_id () id =
          at "metadata/sid" (fun () -> self#visit_symbolic_value_id () id)
        method! visit_mconsumed_symb () value =
          self#visit_symbolic_value_id () value.sv_id;
          self#visit_ty () value.proj_ty
        method! visit_mgiven_back_symb () value =
          self#visit_symbolic_value_id () value.sv_id;
          self#visit_ty () value.proj_ty
        method! visit_ended_proj_borrow_meta () value =
          self#visit_msymbolic_value_id () value.consumed;
          self#visit_msymbolic_value () value.given_back
        method! visit_aended_mut_borrow_meta () value =
          self#visit_msymbolic_value () value.given_back
        method! visit_eended_mut_borrow_meta () value =
          self#visit_msymbolic_value () value.given_back
        method! visit_EValue () captured value =
          self#visit_env () captured;
          self#visit_mvalue () value
        method! visit_EIgnored () value =
          match value with
          | None -> ()
          | Some (captured, value) ->
              self#visit_env () captured;
              self#visit_mvalue () value
      end in
      try
        visitor#visit_env () scan_env;
        ConstGenericVarId.Map.iter (fun _ value -> at "const-generic"
          (fun () -> visitor#visit_tvalue () value)) ctx.const_generic_vars_map;
        if report then List.iter (fun path ->
          Printf.eprintf "DEAD_SHARED_ANALYSIS_REFERENCE owner=%s root=%d sid=%s path=%s\n%!"
            (AbsId.to_string target.abs_id) index (SymbolicValueId.to_string sid) path)
          (List.rev !references);
        !references<>[]
      with Found -> true
    in
    let rec simplify ctx =
      if trace then
        List.iter (function
          | EAbs owner -> List.iteri (fun index root ->
              match InterpRecordedSharedLeaf.loan_at_root root with
              | Some (placement,leaf,(PLeft|PRight as marker),packet) ->
                  let regions=ty_regions packet.proj.proj_ty in
                  let used=used_elsewhere ~report:true ctx owner index packet.proj.sv_id in
                  let placement=match placement with
                    | InterpRecordedSharedLeaf.TopLevel -> "top"
                    | InterpRecordedSharedLeaf.UnderIgnoredSharedLoan -> "ignored-shared-loan" in
                  Printf.eprintf "DEAD_SHARED_ANALYSIS_CANDIDATE owner=%s root=%d sid=%s marker=%s placement=%s kind=%s cont=%b endable=%b ended_levels=%b fixed=%b occurrences=%d empty_history=%b wrapper_type=%b used_elsewhere=%b owned=%s type_regions=%s projected=%s ended_type_regions=%s\n%!"
                    (AbsId.to_string owner.abs_id) index (SymbolicValueId.to_string packet.proj.sv_id)
                    (show_proj_marker marker) placement (show_abs_kind owner.kind)
                    (Option.is_some owner.cont) owner.can_end
                    (not (AbsLevelSet.is_empty owner.ended_subabs))
                    (AbsId.Set.mem owner.abs_id fixed_aids)
                    (List.length(List.filter (function EAbs a -> a.abs_id=owner.abs_id | _ -> false) ctx.env))
                    (packet.consumed=[] && packet.borrows=[])
                    (equal_ty leaf.ty packet.proj.proj_ty) used
                    (RegionId.Set.to_string None owner.regions.owned)
                    (RegionId.Set.to_string None regions)
                    (RegionId.Set.to_string None (RegionId.Set.inter owner.regions.owned regions))
                    (RegionId.Set.to_string None (RegionId.Set.inter regions ctx.ended_regions))
              | _ -> ()) owner.avalues
          | _ -> ()) ctx.env;
      let rec find_in_env = function
        | [] | EFrame :: _ -> None
        | EAbs abs :: rest
          when abs.can_end
               && AbsLevelSet.is_empty abs.ended_subabs
               && not (AbsId.Set.mem abs.abs_id fixed_aids) ->
            let occurrences = List.fold_left (fun n -> function
              | EAbs other when other.abs_id = abs.abs_id -> n + 1
              | _ -> n) 0 ctx.env in
            let candidate = if occurrences <> 1 then None else
              List.find_mapi (fun index (root : tavalue) ->
                match InterpRecordedSharedLeaf.loan_at_root root with
                | Some (placement, leaf, (PLeft | PRight as marker),
                    ({proj; consumed=[]; borrows=[]} as packet))
                  when Types.equal_ty leaf.ty proj.proj_ty
                       && not (RegionId.Set.is_empty abs.regions.owned) ->
                    let route = match placement, abs.kind, abs.cont, root.ty with
                      | InterpRecordedSharedLeaf.TopLevel, Loop _, None, _ ->
                          not (used_elsewhere ctx abs index proj.sv_id)
                      | InterpRecordedSharedLeaf.UnderIgnoredSharedLoan,
                        (WithCont | Loop _), _, TRef(RVar(Free outer),referent,RShared) ->
                          not (RegionId.Set.mem outer abs.regions.owned)
                          && equal_ty referent leaf.ty
                          && InterpRecordedSharedLeaf.count_a proj.sv_id abs = 1
                          && InterpRecordedSharedLeaf.count_e proj.sv_id ctx = 0
                      | _ -> false in
                    if not route then None else
                    let regions = validate_symbolic_hierarchy_type span
                      ctx.crate ctx.type_ctx.type_infos proj.proj_ty in
                    (* A merged owner also owns regions used only by sibling
                       roots. This loan projects exactly the intersection with
                       its own type; those unrelated regions do not make the
                       native dead-projector operation inapplicable. Keep the
                       original full owner mask for native dependency lookup.
                       An unowned region in the full type is not a permission
                       of this projector; native ending still checks every
                       intersecting borrower and concrete dependency. *)
                    let projected=RegionId.Set.inter abs.regions.owned regions in
                    if not (RegionId.Set.is_empty projected)
                       && RegionId.Set.is_empty (RegionId.Set.inter projected ctx.ended_regions)
                    then begin
                      (Invariants.check_typing_invariant_visitor span ctx false)#visit_abs None
                        {abs with avalues=[root];cont=None};
                      Some (abs,index,root,placement,leaf,marker,packet)
                    end else None
                | _ -> None) abs.avalues in
            (match candidate with Some _ -> candidate | None -> find_in_env rest)
        | _ :: rest -> find_in_env rest
      in
      match find_in_env ctx.env with
      | None -> ctx
      | Some (owner,index,root,placement,leaf,marker,packet) ->
          let proj = packet.proj in
          (* The native identity-continuation branch permits this symbolic value
             to survive in concrete values or historical captures. Its two live
             dependency queries, not global SID absence, authorize ending the
             selected projector. The exact environment comparison below retains
             every capture and all unselected current payloads unchanged. *)
          (if Sys.getenv_opt "AENEAS_TRACE_DEAD_SHARED_ANALYSIS_PROJECTIONS" = Some "1" then
            match lookup_intersecting_aproj_borrows_opt span true owner.regions.owned proj ctx with
            | None -> ()
            | Some blockers ->
                List.iter (fun (aid,_,level) ->
                  Printf.eprintf "SHARED_ANALYSIS_BORROWER loan_owner=%s sid=%s borrower=%s level=%d fixed=%b\n%!"
                    (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string proj.sv_id)
                    (AbsId.to_string aid) level (AbsId.Set.mem aid fixed_aids);
                  List.iter (function EAbs a when a.abs_id=aid ->
                    Printf.eprintf "%s\n%!" (abs_to_string span ctx a) | _ -> ()) ctx.env)
                  (blockers.shared_projs @ blockers.non_shared_projs));
          (* The ordinary simplifier below the marker guard already ends
             endable, parent-free abstractions containing only shared reborrows.
             Do that exact native operation early when such a borrower is what
             prevents the selected shared loan from ending. "Fixed" here also
             includes unmarked owners; only can_end=false freezes the native
             simplifier. This route never ends a frozen owner. *)
          let removable_borrower =
            match lookup_intersecting_aproj_borrows_opt span true
                owner.regions.owned proj ctx with
            | Some {non_shared_projs=[]; shared_projs} ->
                List.find_map (fun (aid,_,level) ->
                  if level <> 0 then None else
                  List.find_map (function
                    | EAbs abs when abs.abs_id=aid && abs.can_end
                        && AbsId.Set.is_empty abs.parents
                        && AbsLevelSet.is_empty abs.ended_subabs
                        && Option.is_none abs.cont ->
                        (match abs.avalues with
                        | [{value=ABorrow(AProjSharedBorrow [AsbProjReborrows q]);_}]
                          when q.sv_id=proj.sv_id -> Some abs
                        | _ -> None)
                    | _ -> None) ctx.env) shared_projs
            | _ -> None in
          match removable_borrower with
          | Some borrower ->
              if Sys.getenv_opt "AENEAS_TRACE_DEAD_SHARED_ANALYSIS_PROJECTIONS" = Some "1" then
                Invariants.trace_missing_symbolic_loans span "before early shared-reborrow end" ctx;
              let native,_ = InterpBorrows.end_abs config span ~snapshots:false
                borrower.abs_id 0 ctx in
              let expected_env = List.filter (function
                | EAbs abs when abs == borrower -> false | _ -> true) ctx.env in
              [%cassert] span
                (InterpRecordedSharedLeafPreservation.same_env expected_env native.env
                 && RegionId.Set.equal native.ended_regions
                    (RegionId.Set.union ctx.ended_regions borrower.regions.owned))
                "Early shared reborrow ending changed an unrelated payload";
              if Sys.getenv_opt "AENEAS_TRACE_DEAD_SHARED_ANALYSIS_PROJECTIONS" = Some "1" then
                Printf.eprintf "EARLY_SHARED_REBORROW_END owner=%s sid=%s\n%!"
                  (AbsId.to_string borrower.abs_id) (SymbolicValueId.to_string proj.sv_id);
              simplify native
          | None ->
          let native = InterpBorrows.end_unblocked_proj_loans span owner.abs_id
            owner.regions.owned proj ctx in
          let ended = {leaf with value=ASymbolic(marker,AEndedProjLoans {
            proj_ty=proj.proj_ty;proj=proj.sv_id;consumed=[];borrows=[]})} in
          let expected_root = InterpRecordedSharedLeaf.replace_leaf placement root ended in
          let expected_owner = {owner with avalues=List.mapi
            (fun i old -> if i=index then expected_root else old) owner.avalues} in
          let expected_env = List.map (function
            | EAbs abs when abs == owner -> EAbs expected_owner
            | entry -> entry) ctx.env in
          [%cassert] span (InterpRecordedSharedLeafPreservation.same_env expected_env native.env)
            "Dead shared analysis ending changed an unselected payload or continuation";
          if Sys.getenv_opt "AENEAS_TRACE_DEAD_SHARED_ANALYSIS_PROJECTIONS" = Some "1" then
            Printf.eprintf "DEAD_SHARED_ANALYSIS_PROJECTION abs=%s sid=%s\n%!"
              (AbsId.to_string owner.abs_id) (SymbolicValueId.to_string proj.sv_id);
          simplify native
    in
    simplify ctx

let collapse_ctx_aux config (span : Meta.span) recorded_packet_merges recorded_shared_components
    (recorded_shared_leaves : InterpRecordedSharedLeaf.right_shared_leaf list ref option)
    (sequence : (abs_id * abs_id * abs_id) list ref option)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_or_proj * ty) list ref option)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool)
    (merge_funs : merge_duplicates_funcs) (ctx0 : eval_ctx) : eval_ctx =
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx0];
  Option.iter (fun actions ->
    [%cassert] span (!actions=[] && with_abs_conts && Option.is_some sequence
      && InterpPacketRouting.enabled ())
      "Recorded packet merge: requires a fresh local synthesis route") recorded_packet_merges;
  Option.iter (fun actions ->
    [%cassert] span (!actions = [] && with_abs_conts
      && InterpRecordedSharedLeaf.enabled ()
      && Option.is_some sequence && Option.is_some shared_borrows_seq)
      "Recorded shared leaf: requires fresh local recorded synthesis route")
    recorded_shared_leaves;
  Option.iter (fun actions ->
    [%cassert] span (!actions=[] && with_abs_conts && Option.is_some sequence
      && InterpRecordedSharedLeaf.enabled ())
      "Recorded shared component: requires a fresh local synthesis route") recorded_shared_components;
  let fixed_aids =
    (* We forbid modifying the abs which are frozen or which don't have any markers *)
    let frozen = ctx_get_frozen_abs_set ctx0 in
    let abs = AbsId.Map.values (ctx_get_abs ctx0) in
    let no_markers =
      List.filter_map
        (fun (abs : abs) ->
          if abs_has_markers abs then None else Some abs.abs_id)
        abs
    in
    AbsId.Set.add_list no_markers frozen
  in

  [%ldebug "fixed_aids: " ^ AbsId.Set.to_string None fixed_aids];

  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedMask.retire_cycles config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ~abs_kind:fresh_abs_kind ~merge_funs ctx0
    else ctx0 in
  let ctx =
    reduce_ctx_with_markers ?recorded_packet_merges (Some merge_funs) sequence span ~with_abs_conts
      fresh_abs_kind fixed_aids ctx
  in
  [%ldebug "ctx after reduce:\n" ^ eval_ctx_to_string ctx];
  let ctx =
    collapse_ctx_collapse ?recorded_packet_merges span ~with_abs_conts sequence fresh_abs_kind
      merge_funs ctx
  in
  [%ldebug "ctx after reduce and collapse:\n" ^ eval_ctx_to_string ctx];

  let ctx = eliminate_shared_borrow_markers span shared_borrows_seq ctx in
  [%ldebug
    "ctx after reduce, collapse and eliminate_shared_borrow_markers:\n"
    ^ eval_ctx_to_string ctx];

  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedComponent.retire config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ctx
    else ctx in
  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedProjector.retire config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ctx
    else ctx in
  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedConcrete.retire config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ctx
    else ctx in
  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedMask.retire config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ctx
    else ctx in
  let ctx = end_dead_shared_analysis_projections config span ~with_abs_conts
    ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
    fixed_aids ctx in
  let ctx, pending_components = match recorded_shared_components with
    | None -> ctx,[]
    | Some _ ->
        let chronological_merges=List.rev (Option.get sequence |> (!)) in
        let rec run ctx actions =
          let candidate=List.find_map (function
            | EAbs owner when not (AbsId.Set.mem owner.abs_id fixed_aids) ->
                InterpClosedSharedComponent.choose ~marker:PRight owner
            | _ -> None) ctx.env in
          match candidate with
          | None -> ctx,List.rev actions
          | Some component ->
              let action=InterpRecordedSharedComponent.plan span ~original_joined:ctx0
                ~chronological_merges ~fixed_aids ctx component in
              let next=InterpRecordedSharedComponent.apply_planned config span ~fixed_aids action ctx in
              run next (action::actions) in
        run ctx [] in
  let ctx = eliminate_shared_loans span ctx in
  [%ldebug
    "ctx after reduce, collapse and eliminate_shared_loans:\n"
    ^ eval_ctx_to_string ctx];

  let ctx = eliminate_ended_markers span ctx in
  [%ldebug
    "ctx after reduce, collapse and eliminate_ended_markers:\n"
    ^ eval_ctx_to_string ctx];

  (* Record a separate typed program. Never put these actions into the old
     merge triples, and publish nothing until the original marker guard passes. *)
  let ctx, pending_actions = match recorded_shared_leaves with
    | None -> ctx, []
    | Some _ ->
        let chronological_merges = List.rev !(Option.get sequence) in
        let rec run ctx actions =
          let candidate = List.find_map (function
            | EAbs owner -> Option.map (fun i -> owner,i)
                (InterpRecordedSharedLeaf.right_leaf_root_index owner)
            | _ -> None) ctx.env in
          match candidate with
          | None -> ctx, List.rev actions
          | Some (owner, index) ->
              let action = InterpRecordedSharedLeaf.plan_right_leaf span
                ~original_joined:ctx0 ~chronological_merges ~fixed_aids ctx owner index in
              let next = InterpRecordedSharedLeaf.apply_planned_leaf span ~fixed_aids action ctx in
              run next (action :: actions)
        in
        run ctx []
  in
  (* Report the original owner when an unsupported marked shape survives.
     This is read-only diagnostic data; the original guard remains authoritative. *)
  if eval_ctx_has_markers ctx then
    List.iter (function
      | EAbs owner when eval_ctx_has_markers { ctx with env = [EAbs owner] } ->
          Printf.eprintf "COLLAPSE_REMAINING_MARKERS owner=%s\n%s\n%!"
            (AbsId.to_string owner.abs_id) (abs_to_string span ctx owner)
      | _ -> ()) ctx.env;
  (* Sanity check: there are no markers remaining. Never weaken this guard. *)
  [%sanity_check] span (not (eval_ctx_has_markers ctx));
  Option.iter (fun actions -> actions := pending_actions) recorded_shared_leaves;
  Option.iter (fun actions -> actions := pending_components) recorded_shared_components;

  let ctx =
    if InterpSharedPacketSignature.enabled () then
      InterpClosedSharedComponent.normalize_analysis config span ~with_abs_conts
        ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
        ~fixed_aids ctx
    else ctx in

  (* One last cleanup *)
  let ctx, _ =
    InterpBorrows.simplify_dummy_values_useless_abs config span ctx
  in
  (* Native cleanup may remove the last current reference to a historical
     lifetime name. Recompute the same full-environment unused-name check;
     never quotient the remaining live concrete/symbolic lifetimes. *)
  if InterpSharedPacketSignature.enabled () then
    InterpClosedSharedComponent.normalize_analysis config span ~with_abs_conts
      ~recording:(Option.is_some sequence || Option.is_some shared_borrows_seq)
      ~fixed_aids ctx
  else ctx

let mk_collapse_ctx_merge_duplicate_funs (span : Meta.span)
    (fresh_abs_kind : abs_kind) ~(recoverable : bool) ~(with_abs_conts : bool)
    (ctx : eval_ctx) : merge_duplicates_funcs =
  (* Rem.: the merge functions raise exceptions (that we catch). *)
  let module S : MatchJoinState = struct
    let span = span
    let fresh_abs_kind = fresh_abs_kind
    let nabs = ref []
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = ref SymbolicValueId.Map.empty
    let recover = recoverable
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  (* Functions to match avalues (see {!merge_duplicates_funcs}).

     Those functions are used to merge borrows/loans with the *same ids*.

     They will always be called on destructured avalues (whose children are
     [AIgnored] - we enforce that through sanity checks). We rely on the join
     matcher [JM] to match the concrete values (for shared loans for instance).
     Note that the join matcher doesn't implement match functions for avalues
     (see the comments in {!MakeJoinMatcher}.
  *)
  let merge_amut_borrows id ty0 _pm0 (child0 : tavalue) _ty1 _pm1
      (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);

    (* We need to pick a type for the avalue. The types on the left and on the
       right may use different regions: it doesn't really matter (here, we pick
       the one from the left), because we will merge those regions together
       anyway (see the comments for {!merge_into_first_abstraction}).
    *)
    let ty = ty0 in
    let child = child0 in
    let value = ABorrow (AMutBorrow (PNone, id, child)) in
    { value; ty }
  in

  let merge_ashared_borrows id ty0 _pm0 _ ty1 _pm1 _ : tavalue =
    (* Sanity checks *)
    let _ =
      let _, ty0, _ = ty_as_ref ty0 in
      let _, ty1, _ = ty_as_ref ty1 in
      [%sanity_check] span
        (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty0));
      [%sanity_check] span
        (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty1))
    in

    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let value =
      ABorrow (ASharedBorrow (PNone, id, ctx.fresh_shared_borrow_id ()))
    in
    { value; ty }
  in

  let merge_amut_loans id ty0 _pm0 (child0 : tavalue) _ty1 _pm1
      (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);

    (* Same remarks as for [merge_amut_borrows] *)
    let ty = ty0 in
    let child = child0 in
    let value = ALoan (AMutLoan (PNone, id, child)) in
    { value; ty }
  in
  let merge_ashared_loans ids ty0 pm0 (sv0 : tvalue) (child0 : tavalue) ty1
      pm1 (sv1 : tvalue) (child1 : tavalue) : tavalue =
    (* Sanity checks *)
    [%sanity_check] span (is_aignored child0.value);
    [%sanity_check] span (is_aignored child1.value);
    (* Same remarks as for [merge_amut_borrows].

       This time we need to also merge the shared values. We rely on the
       join matcher [JM] to do so.
    *)
    (match sv0.value,sv1.value,ty0,ty1 with
    | VBorrow(VSharedBorrow(bid0,_)),VBorrow(VSharedBorrow(bid1,_)),
      TRef(_,referent0,RShared),TRef(_,referent1,RShared)
      when InterpSharedPacketSignature.enabled () && bid0=bid1
        && equal_ty referent0 referent1
        && equal_ty sv0.ty (Substitute.erase_regions referent0)
        && equal_ty sv1.ty sv0.ty ->
        let target=match referent0 with
          | TRef(RVar(Free region),target,RShared)
            when not (RegionId.Set.mem region ctx.ended_regions)
              && not (ty_has_borrows (Some span) ctx.type_ctx.type_infos target) -> target
          | _ -> [%craise] span "Shared payload merge requires one live borrow-free target" in
        List.iter (fun marker ->
          let original=InterpSharedPacketSignature.lookup_retained_shared_value span ctx marker bid0 in
          [%cassert] span (equal_ty original.ty (Substitute.erase_regions target)
            && not (tvalue_has_loans_or_borrows (Some span) ctx original))
            "Shared payload merge changed its original loan") [pm0;pm1]
        (* Native match_shared_borrows on the same BID creates precisely a
           fresh unique shared-borrow ID and no new abstraction. Different
           source BIDs remain unsupported by this bounded merge callback. *)
    | _ ->
        [%sanity_check] span
          (not (value_has_loans_or_borrows (Some span) ctx sv0.value));
        [%sanity_check] span
          (not (value_has_loans_or_borrows (Some span) ctx sv1.value)));

    let ty = ty0 in
    let child = child0 in
    let sv = M.match_tvalues ctx ctx sv0 sv1 in
    let value = ALoan (ASharedLoan (PNone, ids, sv, child)) in
    { value; ty }
  in
  let merge_aborrow_projs ty0 _pm0 (proj0 : aproj_borrows) _ty1 _pm1
      (proj1 : aproj_borrows) : tavalue =
    let { proj = { sv_id = sv0; proj_ty = proj_ty0 }; loans = loans0 } :
        aproj_borrows =
      proj0
    in
    let { proj = { sv_id = sv1; proj_ty = proj_ty1 }; loans = loans1 } :
        aproj_borrows =
      proj1
    in
    (* Sanity checks *)
    [%sanity_check] span (loans0 = []);
    [%sanity_check] span (loans1 = []);
    [%sanity_check] span (erase_regions proj_ty0 = erase_regions proj_ty1);
    (* Same remarks as for [merge_amut_borrows]. *)
    let ty = ty0 in
    let proj_ty = proj_ty0 in
    let loans = [] in
    [%sanity_check] span (sv0 = sv1);
    let sv_id = sv0 in
    let proj : symbolic_proj = { sv_id; proj_ty } in
    let value = ASymbolic (PNone, AProjBorrows { proj; loans }) in
    { value; ty }
  in
  let merge_aloan_projs ty0 _pm0 (proj0 : aproj_loans) _ty1 _pm1
      (proj1 : aproj_loans) : tavalue =
    let {
      proj = { sv_id = sv0; proj_ty = proj_ty0 };
      consumed = consumed0;
      borrows = borrows0;
    } : aproj_loans =
      proj0
    in
    let {
      proj = { sv_id = sv1; proj_ty = proj_ty1 };
      consumed = consumed1;
      borrows = borrows1;
    } : aproj_loans =
      proj1
    in
    (* Sanity checks *)
    [%sanity_check] span (consumed0 = [] && borrows0 = []);
    [%sanity_check] span (consumed1 = [] && borrows1 = []);
    [%sanity_check] span (erase_regions proj_ty0 = erase_regions proj_ty1);
    (* Same remarks as for [merge_amut_borrows]. *)
    let ty = ty0 in
    let proj_ty = proj_ty0 in
    let consumed = [] in
    let borrows = [] in
    [%sanity_check] span (sv0 = sv1);
    let sv_id = sv0 in
    let proj : symbolic_proj = { sv_id; proj_ty } in
    let value = ASymbolic (PNone, AProjLoans { proj; consumed; borrows }) in
    { value; ty }
  in
  {
    merge_amut_borrows;
    merge_ashared_borrows;
    merge_amut_loans;
    merge_ashared_loans;
    merge_aborrow_projs;
    merge_aloan_projs;
  }

let merge_into_first_abstraction (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(recoverable : bool) ~(with_abs_conts : bool)
    (ctx : eval_ctx) (aid0 : AbsId.id) (aid1 : AbsId.id) : eval_ctx * AbsId.id =
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span abs_kind ~recoverable
      ~with_abs_conts ctx
  in
  InterpAbs.merge_into_first_abstraction span abs_kind ~can_end ~with_abs_conts
    (Some merge_funs) ctx aid0 aid1

let collapse_ctx config (span : Meta.span) ?recorded_packet_merges ?recorded_shared_components
    ?(recorded_shared_leaves : InterpRecordedSharedLeaf.right_shared_leaf list ref option = None)
    ?(sequence : (abs_id * abs_id * abs_id) list ref option = None)
    ?(shared_borrows_seq :
        (abs_id * int * proj_marker * borrow_or_proj * ty) list ref option =
      None) (fresh_abs_kind : abs_kind) ~(recoverable : bool)
    ~(with_abs_conts : bool) (ctx : eval_ctx) : eval_ctx =
  [%ldebug "Initial ctx:\n" ^ eval_ctx_to_string ctx];
  let merge_funs =
    mk_collapse_ctx_merge_duplicate_funs span fresh_abs_kind ~recoverable
      ~with_abs_conts ctx
  in
  try
    collapse_ctx_aux config span recorded_packet_merges recorded_shared_components ~with_abs_conts recorded_shared_leaves sequence shared_borrows_seq
      fresh_abs_kind merge_funs ctx
  with ValueMatchFailure _ -> [%internal_error] span

let add_shared_borrows (span : Meta.span)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_or_proj * ty) list) (ctx : eval_ctx)
    : eval_ctx =
  let loans, loan_projs = get_non_marked_shared_loans span ctx in
  let ctx = ref ctx in
  let update
      ((abs_id, i, pm, borrow_or_proj, ty) :
        abs_id * int * proj_marker * borrow_or_proj * ty) : unit =
    let abs = ctx_lookup_abs !ctx abs_id in
    let rid = RegionId.Set.choose abs.regions.owned in
    let r : region = RVar (Free rid) in
    let rec update_avalues (i : int) (avl : tavalue list) : tavalue list =
      if i = 0 then
        let nv : tavalue =
          match borrow_or_proj with
          | Borrow bid ->
              [%sanity_check] span (BorrowId.Set.mem bid loans);
              (* TODO: having to insert a type here is really annoying *)
              [%sanity_check] span (ty_no_regions ty);
              {
                value =
                  ABorrow
                    (ASharedBorrow (pm, bid, !ctx.fresh_shared_borrow_id ()));
                ty = mk_ref_ty r ty RShared;
              }
          | Proj (regions', proj) ->
              [%sanity_check] span
                (let proj = normalize_symbolic_proj abs.regions.owned proj in
                 NormSymbProj.Set.mem proj loan_projs);
              (* Substitute the regions with the one we picked *)
              let proj_ty =
                Substitute.ty_subst_rids span
                  (fun rid' ->
                    if RegionId.Set.mem rid' regions' then rid else rid')
                  proj.proj_ty
              in
              let proj = { proj with proj_ty } in
              let value = ASymbolic (pm, AProjBorrows { proj; loans = [] }) in
              let ty = proj.proj_ty in
              { value; ty }
        in
        nv :: avl
      else
        match avl with
        | [] -> [%internal_error] span
        | av :: avl' -> av :: update_avalues (i - 1) avl'
    in
    let abs = { abs with avalues = update_avalues i abs.avalues } in
    let ctx', _ = ctx_subst_abs span !ctx abs.abs_id abs in
    ctx := ctx'
  in
  List.iter update shared_borrows_seq;

  !ctx

(** Collapse a context following a sequence *)
let collapse_ctx_following_sequence config (span : Meta.span) ~recorded_packet_merges ~recorded_shared_components
    ~(recorded_shared_leaves : InterpRecordedSharedLeaf.right_shared_leaf list)
    ~(recorded_fixed_aids : AbsId.Set.t option)
    (sequence : (abs_id * abs_id * abs_id) list)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_or_proj * ty) list)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool) (ctx0 : eval_ctx) :
    eval_ctx =
  [%ltrace
    "- ctx0:\n" ^ eval_ctx_to_string ctx0 ^ "\n- sequence:\n"
    ^ String.concat "\n"
        (List.map
           (fun (a0, a1, a2) ->
             "(" ^ AbsId.to_string a0 ^ "," ^ AbsId.to_string a1 ^ ") -> "
             ^ AbsId.to_string a2)
           sequence)];
  let action_ids=List.map fst recorded_packet_merges in
  InterpPacketRouting.require span
    (List.length action_ids=List.length (List.sort_uniq Stdlib.compare action_ids)
     && List.for_all (fun id -> List.exists (fun (_,_,result)->result=id) sequence) action_ids)
    "recorded right packet actions do not identify unique merge steps";
  let ctx = ref ctx0 in
  let nabs_map = ref AbsId.Map.empty in
  let get_id (aid : abs_id) : abs_id =
    match AbsId.Map.find_opt aid !nabs_map with
    | None -> aid
    | Some aid -> aid
  in

  (* Apply the sequence of merges *)
  List.iter
    (fun (abs0, abs1, nabs) ->
      (* Substitute - the ids may have changed *)
      let abs0 = get_id abs0 in
      let abs1 = get_id abs1 in
      let packet_replay=List.assoc_opt nabs recorded_packet_merges in
      let packet_fixed_abs_ids=Option.map (fun action ->
        AbsId.Set.fold (fun id ids -> AbsId.Set.add (get_id id) ids)
          (InterpPacketRouting.recorded_fixed action) (ctx_get_frozen_abs_set !ctx)) packet_replay in
      Option.iter (fun _ ->
        InterpPacketRouting.require span
          (Option.is_some (ctx_lookup_abs_opt !ctx abs0)
           && Option.is_some (ctx_lookup_abs_opt !ctx abs1))
          "right packet replay lost a recorded right owner") packet_replay;
      (* Attempt to merge - note that some region might be missing, because
         it appears only in one environment and not the other *)
      match (ctx_lookup_abs_opt !ctx abs0, ctx_lookup_abs_opt !ctx abs1) with
      | Some _, Some _ ->
          (* Merge and register the new id *)
          [%ldebug
            "Merging: " ^ AbsId.to_string abs0 ^ " <- " ^ AbsId.to_string abs1];
          let nctx, nabs' =
            InterpAbs.merge_into_first_abstraction ?packet_fixed_abs_ids ?packet_replay
              span fresh_abs_kind ~can_end:true ~with_abs_conts None !ctx abs0 abs1
          in
          ctx := nctx;
          Option.iter (fun action ->
            Printf.eprintf "RECORDED_PACKET_REPLAYED recorded=%s result=%s %s\n%!"
              (AbsId.to_string nabs) (AbsId.to_string nabs')
              (InterpPacketRouting.recorded_description action)) packet_replay;
          [%ldebug
            "Context after merging " ^ AbsId.to_string nabs' ^ " := ("
            ^ AbsId.to_string abs0 ^ " <- " ^ AbsId.to_string abs1 ^ "):\n"
            ^ eval_ctx_to_string !ctx];
          nabs_map := AbsId.Map.add nabs nabs' !nabs_map
      | None, Some abs | Some abs, None ->
          (* We don't have to merge anything, meaning the abstraction resulting
             from the merge is exactly the abstraction we found (what happened is
             that we're in the situation where we had to merge an abstraction
             from one side with another abstracction from the other side). *)
          [%ldebug
            "Registering: " ^ AbsId.to_string nabs ^ " --> "
            ^ AbsId.to_string abs.abs_id];
          nabs_map := AbsId.Map.add nabs abs.abs_id !nabs_map
      | None, None ->
          (* The two abs come from the unprojected environment: we don't have to
             merge anything *)
          [%ldebug
            "Could not find left abstraction " ^ AbsId.to_string abs0
            ^ " and right abstraction " ^ AbsId.to_string abs1
            ^ " in context:\n" ^ eval_ctx_to_string !ctx])
    sequence;
  let ctx = !ctx in
  [%ldebug "ctx after applying the merge sequence:\n" ^ eval_ctx_to_string ctx];

  let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
  let ctx = reorder_fresh_abs span true fixed_aids ctx in
  [%ldebug "ctx after reordering the fresh abs:\n" ^ eval_ctx_to_string ctx];

  (* Update the ids used in the sequence of shared borrows *)
  let shared_borrows_seq =
    List.map
      (fun (abs_id, i, pm, bid, ty) ->
        (AbsId.Map.find abs_id !nabs_map, i, pm, bid, ty))
      shared_borrows_seq
  in
  let ctx = add_shared_borrows span shared_borrows_seq ctx in
  [%ldebug "ctx after adding the shared borrows:\n" ^ eval_ctx_to_string ctx];

  let ctx = match recorded_shared_components with
    | [] -> ctx
    | actions ->
        [%cassert] span with_abs_conts "Recorded shared component: replay requires synthesis";
        let fixed_aids=match recorded_fixed_aids with
          | Some ids -> AbsId.Set.union ids (ctx_get_frozen_abs_set ctx)
          | None -> [%craise] span "Recorded shared component: replay missing original fixed IDs" in
        List.fold_left (fun ctx action ->
          InterpRecordedSharedComponent.replay config span ~resolve_owner:get_id
            ~fixed_aids action ctx) ctx actions in
  let ctx = eliminate_shared_loans span ctx in
  [%ldebug "ctx after eliminating the shared loans:\n" ^ eval_ctx_to_string ctx];

  (* Revalidate only after all merges, reordering, shared-borrow introductions,
     and the original concrete cleanup. The old sequence program is unchanged. *)
  match recorded_shared_leaves with
  | [] -> ctx
  | actions ->
      [%cassert] span (with_abs_conts && InterpRecordedSharedLeaf.enabled ())
        "Recorded shared leaf: replay requires enabled synthesis route";
      let fixed_aids = match recorded_fixed_aids with
        | Some ids -> AbsId.Set.union ids (ctx_get_frozen_abs_set ctx)
        | None -> [%craise] span "Recorded shared leaf: replay missing original fixed IDs" in
      let ctx = List.fold_left (fun ctx action ->
        InterpRecordedSharedLeaf.replay_right_leaf span ~resolve_owner:get_id
          ~fixed_aids action ctx) ctx actions in
      Invariants.check_invariants span ctx;
      ctx

let collapse_ctx_no_markers_following_sequence config (span : Meta.span)
    ?(recorded_packet_merges = []) ?(recorded_shared_components = [])
    ?(recorded_shared_leaves : InterpRecordedSharedLeaf.right_shared_leaf list = [])
    ?(recorded_fixed_aids : AbsId.Set.t option = None)
    (sequence : (abs_id * abs_id * abs_id) list)
    (shared_borrows_seq :
      (abs_id * int * proj_marker * borrow_or_proj * ty) list)
    (fresh_abs_kind : abs_kind) ~(with_abs_conts : bool) (ctx : eval_ctx) :
    eval_ctx =
  try
    collapse_ctx_following_sequence config span ~recorded_packet_merges ~recorded_shared_components ~with_abs_conts ~recorded_shared_leaves
      ~recorded_fixed_aids sequence
      shared_borrows_seq fresh_abs_kind ctx
  with ValueMatchFailure _ -> [%internal_error] span
