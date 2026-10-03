(** Checked preparation for a packet-preserving abstraction merge.
    This module edits only the certified complementary A subtrees. It neither
    commits an environment nor supplies an alternative continuation semantics. *)
open Types
open Values
module P = InterpPacketInterface
module C = InterpExternalPermissions
exception Unsupported of string
let require b s = if not b then raise (Unsupported s)
let fail s = raise (Unsupported s)

let index text length =
  match int_of_string_opt text with
  | Some i when i >= 0 && i < length && string_of_int i = text -> i
  | _ -> fail "noncanonical or out-of-range packet path index"
let update_at i f xs = List.mapi (fun j x -> if i=j then f x else x) xs

(** Following one explicit path preserves all untouched sibling and metadata
    objects. In particular, an ended ignored wrapper is not flattened. *)
let rec replace_value path marker original (value:tavalue) : tavalue =
  let changed = match path,value.value with
    | ["packet"],ASymbolic(pm,p) ->
        require(pm=marker && p==original)"selected projector identity/marker changed";
        ASymbolic(PNone,AEmpty)
    | "field"::n::tail,AAdt a ->
        let i=index n (List.length a.fields) in
        AAdt {a with fields=update_at i (replace_value tail marker original) a.fields}
    | "child"::tail,ABorrow(AMutBorrow(pm,id,c)) ->
        ABorrow(AMutBorrow(pm,id,replace_value tail marker original c))
    | "child"::tail,ABorrow(AIgnoredMutBorrow(id,c)) ->
        ABorrow(AIgnoredMutBorrow(id,replace_value tail marker original c))
    | "child"::tail,ABorrow(AEndedMutBorrow(m,c)) ->
        ABorrow(AEndedMutBorrow(m,replace_value tail marker original c))
    | "child"::tail,ABorrow(AEndedIgnoredMutBorrow b) ->
        ABorrow(AEndedIgnoredMutBorrow {b with child=replace_value tail marker original b.child})
    | "given_back"::tail,ABorrow(AEndedIgnoredMutBorrow b) ->
        ABorrow(AEndedIgnoredMutBorrow {b with given_back=replace_value tail marker original b.given_back})
    | "child"::tail,ALoan(AMutLoan(pm,id,c)) ->
        ALoan(AMutLoan(pm,id,replace_value tail marker original c))
    | "child"::tail,ALoan(ASharedLoan(pm,id,v,c)) ->
        ALoan(ASharedLoan(pm,id,v,replace_value tail marker original c))
    | "child"::tail,ALoan(AIgnoredMutLoan(id,c)) ->
        ALoan(AIgnoredMutLoan(id,replace_value tail marker original c))
    | "child"::tail,ALoan(AIgnoredSharedLoan c) ->
        ALoan(AIgnoredSharedLoan(replace_value tail marker original c))
    | "child"::tail,ALoan(AEndedSharedLoan(v,c)) ->
        ALoan(AEndedSharedLoan(v,replace_value tail marker original c))
    | "child"::tail,ALoan(AEndedMutLoan b) ->
        ALoan(AEndedMutLoan {b with child=replace_value tail marker original b.child})
    | "given_back"::tail,ALoan(AEndedMutLoan b) ->
        ALoan(AEndedMutLoan {b with given_back=replace_value tail marker original b.given_back})
    | "child"::tail,ALoan(AEndedIgnoredMutLoan b) ->
        ALoan(AEndedIgnoredMutLoan {b with child=replace_value tail marker original b.child})
    | "given_back"::tail,ALoan(AEndedIgnoredMutLoan b) ->
        ALoan(AEndedIgnoredMutLoan {b with given_back=replace_value tail marker original b.given_back})
    | _ -> fail "selected path is not a typed projector root"
  in {value with value=changed}

let replace_root (owner:abs) (selected:P.packet) =
  match selected.at.surface,selected.at.path,selected.at.original with
  | P.A,"avalue"::n::tail,P.APacket original ->
      let i=index n (List.length owner.avalues) in
      {owner with avalues=update_at i (replace_value tail selected.marker original) owner.avalues}
  | _ -> fail "selected packet is not an owner A root"

let same_original left right = match left,right with
  | P.AValue a,P.AValue b -> a==b
  | P.EValue a,P.EValue b -> a==b
  | P.APacket a,P.APacket b -> a==b
  | P.EPacket a,P.EPacket b -> a==b
  | P.ConsumedMetadata a,P.ConsumedMetadata b -> a==b
  | P.SymbolicMetadata a,P.SymbolicMetadata b -> a==b
  | P.ConcreteMetadata a,P.ConcreteMetadata b -> a==b
  | P.SharedReborrow a,P.SharedReborrow b -> a==b
  | _ -> false
let same_key (a:P.node) (b:P.node) = a.surface=b.surface && a.path=b.path
let find_node nodes node = match List.filter (fun x->same_key x node) nodes with
  | [x] -> x | _ -> fail "residual node absent or ambiguous"

(** The output must contain precisely the old nodes outside the selected
    subtree, its rebuilt typed ancestors, and one explicit empty placeholder. *)
let check_conservation (before:P.descriptor) (after:P.descriptor) selected_path =
  let below (n:P.node) = n.surface=P.A && P.prefix selected_path n.path in
  let ancestor (n:P.node) = n.surface=P.A && P.prefix n.path selected_path in
  List.iter (fun (old:P.node) ->
    if not (below old) then begin
      let fresh=find_node after.nodes old in
      require(old.level=fresh.level)"retained node level changed";
      if not(ancestor old) then
        require(same_original old.original fresh.original)"untouched node identity changed"
      else match old.original,fresh.original with
        | P.AValue a,P.AValue b -> require(a.ty==b.ty)"ancestor native type changed"
        | _ -> fail "selected path crosses a non-value ancestor"
    end) before.nodes;
  List.iter (fun (fresh:P.node) ->
    if fresh.surface=P.A && fresh.path=selected_path then
      (match fresh.original with P.APacket AEmpty -> () | _->fail "missing empty placeholder")
    else begin
      require(not(below fresh))"selected history retained after cancellation";
      ignore(find_node before.nodes fresh)
    end) after.nodes;
  require(after.owner.cont==before.owner.cont)"preparation changed continuation"

(** Only regular current types are interpreted by this owner's region set.
    Historical metadata and saved environments retain their source provenance.
    Adding the other owner's regions must not broaden any retained current
    value, projection, pattern or shared-reborrow interpretation. *)
let check_union_masks ctx (d:P.descriptor) owned =
  let additional=RegionId.Set.diff owned d.owner.regions.owned in
  let checks=ref 0 in
  let check ty =
    incr checks;
    let info=P.view_type ctx d.owner ty in
    require(RegionId.Set.is_empty(RegionId.Set.inter additional info.free_regions))
      "owned union broadens a retained regular projection or wrapper"
  in
  List.iter(fun (n:P.node)->match n.original with
    | P.AValue v -> check v.ty
    | P.EValue v -> check v.ty
    | P.SharedReborrow(AsbProjReborrows p) -> check p.proj_ty
    | _ -> ()) d.nodes;
  List.iter(fun (p:P.packet)->if p.polarity<>P.Empty then check p.typ.full)d.packets;
  List.iter(fun (b:P.binding_site)->check b.pattern.ty)d.bindings;
  !checks

(** The additional level-one cancellation must not discard a current E
    interface or a captured value referring to that child. Saved environments
    are used only to resolve the actual captured value; unrelated historical
    bindings are not promoted to current interfaces. This is a conservative
    admission check, not a proof of continuation effects. *)
let check_child_e_boundary ?current_env span ctx owners child_sid =
  let checks=ref 0 in
  let ignored_roots=ref [] in
  let rec concrete snapshot marker ancestors bids (value:tvalue) =
    require(not(List.exists(fun x->x==value)ancestors))
      "cyclic captured value in child E boundary";
    let ancestors=value::ancestors in
    match value.value with
    | VSymbolic s ->
        incr checks;
        require(s.sv_id<>child_sid)"cancelled child has a captured E value"
    | VLiteral _ | VBottom | VLoan(VMutLoan _) -> ()
    | VAdt a -> List.iter(concrete snapshot marker ancestors bids)a.fields
    | VBorrow(VMutBorrow(_,v)) | VLoan(VSharedLoan(_,v)) ->
        concrete snapshot marker ancestors bids v
    | VBorrow(VSharedBorrow(bid,_) | VReservedMutBorrow(bid,_)) ->
        require(not(BorrowId.Set.mem bid bids))"cyclic captured shared borrow";
        let saved=match snapshot with Some env->env
          | None->fail "shared concrete metadata has no captured environment" in
        let borrowed=match marker with
          | None -> [None,InterpBorrowsCore.lookup_shared_value span saved bid]
          | Some marker ->
              InterpSharedPacketSignature.lookup_retained_shared_values_for_inventory_in_env
                span ~type_infos:ctx.P.type_ctx.type_infos ~ended_regions:ctx.ended_regions
                saved marker bid
              |> List.map (fun (marker,value)->Some marker,value) in
        List.iter (fun (marker,v)->
          concrete snapshot marker ancestors (BorrowId.Set.add bid bids) v) borrowed
  in
  List.iter(fun owner ->
    let d=P.describe_owner ctx owner in
    List.iter(fun (p:P.packet)->if p.at.surface<>P.A then begin
      incr checks;
      require(p.sid<>Some child_sid)"cancelled child has a current E projector"
    end)d.packets;
    List.iter(fun (m:P.metadata)->if m.at.surface<>P.A then begin
      incr checks;
      require(m.sid<>child_sid)"cancelled child has current E history metadata"
    end)d.metadata;
    List.iter(fun (c:P.capture)->
      concrete (Some c.snapshot) None [] BorrowId.Set.empty c.value)d.captures;
    (* These fields are opaque to generic visitors, but some ended-loan
       given-back values are consumed by the real Pure translation. Unlike
       captures, they carry no saved environment for shared dereferencing. *)
    List.iter(fun (m:P.concrete_metadata)->
      let unused_root = match m.at.surface,m.at.path with
        | P.A,["avalue";n;"ignored_meta"] ->
            let i=index n (List.length owner.avalues) in
            (match (List.nth owner.avalues i).value with
             | AIgnored(Some original) -> original==m.value
             | _ -> false)
        | _ -> false in
      (* abs_to_consumed calls each top-level avalue with filter=true.
         A root AIgnored returns None without reading metadata. Its original
         wrapper and root position are preserved by this merge. This exemption
         does NOT cover ignored ADT fields or any ended-loan given-back value.
         Corresponding E captures, when present, are checked above. *)
      let unused_ignored_loan =
        List.exists (fun (n:P.node) ->
          n.surface=P.A && m.at.surface=P.A && n.level=m.at.level
          && m.at.path=n.path@["given_back_meta"]
          && match n.original with
             | P.AValue {value=ALoan(AEndedIgnoredMutLoan ended);_} ->
                 ended.given_back_meta==m.value
             | _ -> false) d.nodes in
      (* The native consumed and given-back translations of exactly
         AEndedIgnoredMutLoan both ignore this metadata and traverse its two
         child trees at their own levels (SymbolicToPureValues). Retain the
         original field; do not resolve its historical shared borrows using
         today's environment. Owned AEndedMutLoan metadata and every E capture
         remain checked, as do all metadata nodes inside either child tree. *)
      (* A current ASharedLoan payload is a runtime value, even though the
         descriptor groups it with opaque concrete fields. Resolve only this
         exact original payload in the complete current environment, retaining
         every marked branch. Historical ended-loan fields still require their
         own captured provenance and never fall back to today's environment. *)
      let current_marker=List.find_map (fun (n:P.node)->
        if n.surface=P.A && m.at.surface=P.A && n.level=m.at.level
          && m.at.path=n.path@["shared_value"] then
          match n.original with
          | P.AValue {value=ALoan(ASharedLoan(marker,_,payload,_));_}
            when payload==m.value -> Some marker
          | _ -> None
        else None) d.nodes in
      if unused_root then ignored_roots:=m::!ignored_roots
      else if unused_ignored_loan then ()
      else
      try (match current_marker,current_env with
        | Some marker,Some env -> concrete (Some env) (Some marker) [] BorrowId.Set.empty m.value
        | _ -> concrete None None [] BorrowId.Set.empty m.value)
      with Unsupported reason ->
        fail("owner"^AbsId.to_string owner.abs_id^"/"^
          String.concat "/" m.at.path^": "^reason
          ^ "\noriginal concrete metadata: " ^ show_tvalue m.value))d.concrete_metadata) owners;
  !checks,List.rev !ignored_roots

type prepared = {
  closure : C.report;
  original_loan_owner : abs;
  original_borrow_owner : abs;
  loan_owner : abs;
  borrow_owner : abs;
  loan_descriptor : P.descriptor;
  borrow_descriptor : P.descriptor;
  owned : RegionId.Set.t;
  parents : AbsId.Set.t;
  regular_mask_checks : int;
  child_e_checks : int;
  ignored_root_metadata : P.concrete_metadata list;
  (** Exact removed nodes, including both history-edge metadata objects. These
      witnesses describe the new cancellation rule; they are not retained in
      the resulting A tree and their removal is not a preservation theorem. *)
  removed_loan_nodes : P.node list;
  removed_borrow_nodes : P.node list;
}

let prepare ?(with_abs_conts=true) ?(allow_marked=false) span ~native_type_ctx (ctx:P.context) ~current_env ~supplied_env
    ~fixed_aids ~loan_owner ~loan_path ~borrow_owner ~borrow_path =
  let closure=C.check ~allow_marked span ~native_type_ctx ctx ~current_env ~supplied_env
    ~fixed_aids ~loan_owner ~loan_path ~borrow_owner ~borrow_path in
  if not closure.closed_in_supplied_current_environment then begin
    let occurrence (o:C.occurrence) =
      "owner" ^ AbsId.to_string o.owner.abs_id ^ "/" ^ String.concat "/" o.path
      ^ " level=" ^ string_of_int o.level
      ^ " sid=" ^ SymbolicValueId.to_string o.sid
      ^ " polarity=" ^ (match o.polarity with P.Loan->"loan"|P.Borrow->"borrow"|P.Empty->"empty")
      ^ " owned=" ^ RegionId.Set.to_string None o.owner.regions.owned
      ^ "\n" ^ show_ty o.ty in
    let selected_root (owner:abs) path =
      "owner" ^ AbsId.to_string owner.abs_id ^ "/" ^ String.concat "/" path
      ^ "\n" ^ show_aproj (P.original_ap (P.find_packet (P.describe_owner ctx owner) path)) in
    fail ("external packet permission closure failed\nissues:\n"
      ^ String.concat "\n" closure.issues
      ^ "\nrequested loan: " ^ selected_root loan_owner loan_path
      ^ "\nrequested borrow: " ^ selected_root borrow_owner borrow_path
      ^ "\nselected occurrences:\n" ^ String.concat "\n" (List.map occurrence closure.selected)
      ^ "\nexternal occurrences:\n" ^ String.concat "\n" (List.map occurrence closure.external_permissions)
      ^ "\nruntime dependencies:\n" ^ String.concat "\n"
          (List.map (fun (r:C.runtime)->r.path ^ "\n" ^ show_tvalue r.value) closure.runtime_dependencies))
  end;
  let plan=match closure.plan with Some x->x | None->fail "missing recomputed packet plan" in
  List.iter(fun (owner:abs)->
    require(AbsLevelSet.is_empty owner.ended_subabs)"owner has recorded ended sublevels";
    (* Fixed-point analysis may already have merged away its continuations.
       Synthesis must still compose both originals. Any E data that is present
       remains in the descriptors and all boundary/conservation/mask checks. *)
    if with_abs_conts then
      require(Option.is_some owner.cont)"packet synthesis merge requires both original continuations")
    [loan_owner;borrow_owner];
  let marked_shared_packet = allow_marked && plan.paired<>[]
    && List.for_all (fun ((left:P.packet),(right:P.packet)) ->
      left.marker<>PNone && left.marker=right.marker
      && not left.typ.owned_mutable && not right.typ.owned_mutable) plan.paired in
  (* The checked planner admits an ordinary edge or its complete ordered
     reciprocal history tree. Each endpoint retains its branch identity;
     closure covers every selected SID. Owned sets are masks, so the native union is allowed
     only after checking every retained A/E mask below. *)
  require(RegionId.Set.is_empty(RegionId.Set.inter loan_owner.regions.owned borrow_owner.regions.owned)
    || marked_shared_packet)
    "merged owners have overlapping native owned regions outside marked shared cancellation";
  let (left,right),children = match plan.paired with
    | parent::children -> parent,children
    | []->fail "empty complementary packet" in
  let child_e_checks,ignored_root_metadata =
    List.fold_left (fun (checks,ignored) ((child:P.packet),_) ->
      let child_sid=match child.sid with Some x->x | None->fail "child has no SID" in
      let more,metadata=check_child_e_boundary ~current_env span ctx closure.owners child_sid in
      checks+more,List.fold_left (fun kept m ->
        if List.exists (fun original -> original==m) kept then kept else kept@[m])
        ignored metadata) (0,[]) children in
  let edited_left=replace_root loan_owner left and edited_right=replace_root borrow_owner right in
  let ld=P.describe_owner ctx edited_left and bd=P.describe_owner ctx edited_right in
  check_conservation plan.loan_descriptor ld loan_path;
  check_conservation plan.borrow_descriptor bd borrow_path;
  let owned=RegionId.Set.union loan_owner.regions.owned borrow_owner.regions.owned in
  let regular_mask_checks=check_union_masks ctx ld owned + check_union_masks ctx bd owned in
  let parents=AbsId.Set.diff (AbsId.Set.union loan_owner.parents borrow_owner.parents)
    (AbsId.Set.of_list [loan_owner.abs_id;borrow_owner.abs_id]) in
  let removed d path=List.filter(fun (n:P.node)->n.surface=P.A && P.prefix path n.path)d.P.nodes in
  let removed_loan_nodes=removed plan.loan_descriptor loan_path
  and removed_borrow_nodes=removed plan.borrow_descriptor borrow_path in
  {closure;original_loan_owner=loan_owner;original_borrow_owner=borrow_owner;
   loan_owner=edited_left;borrow_owner=edited_right;loan_descriptor=ld;borrow_descriptor=bd;
   owned;parents;regular_mask_checks;child_e_checks;ignored_root_metadata;
   removed_loan_nodes;removed_borrow_nodes}
