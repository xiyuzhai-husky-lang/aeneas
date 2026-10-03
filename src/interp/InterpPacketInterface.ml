(** Read-only, uncommitted packet interface planning. No production caller. *)
open Types
open Values
open Contexts
open InterpBorrowsCore

let unsupported s = [%craise_opt_span] None ("Packet interface: " ^ s)
let require b s = [%cassert_opt_span] None b ("Packet interface: " ^ s)

type context = { type_ctx : Contexts.type_ctx; ended_regions : RegionId.Set.t }
let context_of_eval (ctx : eval_ctx) = {type_ctx=ctx.type_ctx;ended_regions=ctx.ended_regions}
type path = string list
type surface = A | EInput | EOutput
type polarity = Borrow | Loan | Empty
type phase = Live | Ended
type type_origin = ProjectorType | EndedProjectorType | EnclosingType | MetadataType

type type_view = {
  full : ty;
  normalized : ty;
  free_regions : RegionId.Set.t;
  ended_regions : RegionId.Set.t;
  owned_mutable : bool;
}
type original =
  | AValue of tavalue | EValue of tevalue
  | APacket of aproj | EPacket of eproj
  | ConsumedMetadata of mconsumed_symb
  | SymbolicMetadata of msymbolic_value
  | ConcreteMetadata of tvalue
  | SharedReborrow of abstract_shared_borrow

type node = { path : path; surface : surface; level : int; original : original }
type packet = {
  at : node;
  polarity : polarity;
  phase : phase;
  sid : symbolic_value_id option;
  typ : type_view;
  type_origin : type_origin;
}
type metadata = { at : node; sid : symbolic_value_id; typ : type_view }
type capture = {
  at : node;
  snapshot : env;
  value : tvalue;
  (** This is a capture inventory boundary, never a claim that it is bound. *)
}
type concrete_metadata = { at : node; value : tvalue }
type shared_reborrow = { at : node; proj : symbolic_proj option }
type binding_site = { at : node; owned : RegionId.Set.t; pattern : tepat }
type unresolved =
  | ConcreteMetadataDependency of node
  | CaptureBinding of node
  | LetScope of node
  | FreeVariableBinding of node * abs_fvar_id
  | BoundVariableScope of node * abs_bvar
  | ApplicationEffectAndInterface of node * abs_fun
  | BottomExpression of node

type descriptor = {
  owner : abs;
  nodes : node list;
  packets : packet list;
  metadata : metadata list;
  captures : capture list;
  concrete_metadata : concrete_metadata list;
  bindings : binding_site list;
  shared_reborrows : shared_reborrow list;
  unresolved : unresolved list;
}

let view_type (ctx : context) owner ty =
  let regions = ref RegionId.Set.empty in
  let v = object
    inherit [_] iter_ty
    method! visit_region () = function
      | RVar (Free r) -> regions := RegionId.Set.add r !regions
      | RStatic | RErased -> ()
      | _ -> unsupported "bound/body region in interface type"
  end in
  v#visit_ty () ty;
  { full = ty; normalized = normalize_proj_ty owner.regions.owned ty;
    free_regions = !regions;
    ended_regions = RegionId.Set.inter !regions ctx.ended_regions;
    owned_mutable = TypesUtils.ty_has_mut_borrow_for_region_in_set
      ctx.type_ctx.type_infos owner.regions.owned ty }

let describe_owner ctx (owner : abs) : descriptor =
  let nodes = ref [] and packets = ref [] and metadata = ref [] and captures = ref [] in
  let concrete_metadata = ref [] and bindings = ref [] and unresolved = ref [] and shared_reborrows=ref [] in
  let node surface level path original =
    let n = { path; surface; level; original } in nodes := n :: !nodes; n in
  let packet surface level path original polarity phase sid typ type_origin =
    let at = node surface level path original in
    packets := {at; polarity; phase; sid;typ=view_type ctx owner typ;type_origin} :: !packets in
  let meta surface level path (m : mconsumed_symb) =
    let at=node surface level path (ConsumedMetadata m) in
    metadata := {at;sid=m.sv_id;typ=view_type ctx owner m.proj_ty} :: !metadata in
  let sym surface level path (m : msymbolic_value) =
    let at=node surface level path (SymbolicMetadata m) in
    metadata := {at;sid=m.sv_id;typ=view_type ctx owner m.sv_ty} :: !metadata in
  let concrete surface level path value =
    let at=node surface level path (ConcreteMetadata value) in
    concrete_metadata := {at;value} :: !concrete_metadata;
    unresolved:=ConcreteMetadataDependency at::!unresolved in
  let rec ah level path inherited p =
    let save polarity phase sid ty origin = packet A level path (APacket p) polarity phase sid ty origin in
    let history channel xs = List.iteri (fun i (m,c) ->
      let edge=path@[channel;string_of_int i] in meta A level (edge@["metadata"]) m;
      ah (level+1) (edge@["child"]) inherited c) xs in
    match p with
    | AProjBorrows p -> save Borrow Live (Some p.proj.sv_id) p.proj.proj_ty ProjectorType; history "loans" p.loans
    | AProjLoans p -> save Loan Live (Some p.proj.sv_id) p.proj.proj_ty ProjectorType; history "consumed" p.consumed; history "borrows" p.borrows
    | AEndedProjLoans p -> save Loan Ended (Some p.proj) p.proj_ty EndedProjectorType; history "consumed" p.consumed; history "borrows" p.borrows
    | AEndedProjBorrows p -> save Borrow Ended (Some p.mvalues.consumed) p.proj_ty EndedProjectorType;
      sym A level (path@["given_back"]) p.mvalues.given_back; history "loans" p.loans
    | AEmpty -> save Empty Ended None inherited EnclosingType
  and eh surface level path inherited p =
    let save polarity phase sid ty origin = packet surface level path (EPacket p) polarity phase sid ty origin in
    let history channel xs = List.iteri (fun i (m,c) ->
      let edge=path@[channel;string_of_int i] in meta surface level (edge@["metadata"]) m;
      eh surface (level+1) (edge@["child"]) inherited c) xs in
    match p with
    | EProjBorrows p -> save Borrow Live (Some p.proj.sv_id) p.proj.proj_ty ProjectorType; history "loans" p.loans
    | EProjLoans p -> save Loan Live (Some p.proj.sv_id) p.proj.proj_ty ProjectorType; history "consumed" p.consumed; history "borrows" p.borrows
    | EEndedProjLoans p -> save Loan Ended (Some p.proj) p.proj_ty EndedProjectorType; history "consumed" p.consumed; history "borrows" p.borrows
    | EEndedProjBorrows p -> save Borrow Ended (Some p.mvalues.consumed) p.proj_ty EndedProjectorType;
      sym surface level (path@["given_back"]) p.mvalues.given_back; history "loans" p.loans
    | EEmpty -> save Empty Ended None inherited EnclosingType
  and av level path (v : tavalue) =
    ignore(node A level path (AValue v)); ignore(view_type ctx owner v.ty);
    let child = av level (path@["child"]) and given = av (level+1) (path@["given_back"]) in
    match v.value with
    | AAdt a -> List.iteri(fun i c -> av level (path@["field";string_of_int i]) c)a.fields
    | ASymbolic (pm,p) -> require(pm=PNone)"marked A packet"; ah level (path@["packet"]) v.ty p
    | AIgnored m -> Option.iter (concrete A level (path@["ignored_meta"])) m
    | ABorrow b -> (match b with
      | AEndedIgnoredMutBorrow b -> child b.child; given b.given_back; sym A level (path@["given_back_meta"]) b.given_back_meta
      | AEndedMutBorrow (m,c) -> sym A level (path@["given_back_meta"])m.given_back; child c
      | AMutBorrow (_,_,c) | AIgnoredMutBorrow (_,c) -> child c
      | AProjSharedBorrow xs -> List.iteri(fun i x ->
        let at=node A level(path@["shared_reborrow";string_of_int i])(SharedReborrow x)in
        let proj=match x with AsbProjReborrows p->Some p|AsbBorrow _->None in
        shared_reborrows:={at;proj}::!shared_reborrows)xs
      | ASharedBorrow _ | AEndedSharedBorrow -> ())
    | ALoan l -> (match l with
      | AEndedMutLoan l -> concrete A level(path@["given_back_meta"])l.given_back_meta;given l.given_back;child l.child
      | AEndedIgnoredMutLoan l -> concrete A level(path@["given_back_meta"])l.given_back_meta;given l.given_back;child l.child
      | ASharedLoan (_,_,sv,c) | AEndedSharedLoan (sv,c) -> concrete A level(path@["shared_value"])sv;child c
      | AMutLoan (_,_,c) | AIgnoredMutLoan (_,c) | AIgnoredSharedLoan c -> child c)
  and ev surface level path (v : tevalue) =
    let at=node surface level path (EValue v) in ignore(view_type ctx owner v.ty);
    let child = ev surface level (path@["child"]) and given = ev surface (level+1) (path@["given_back"]) in
    match v.value with
    | EAdt a -> List.iteri(fun i c -> ev surface level (path@["field";string_of_int i])c)a.fields
    | ESymbolic (pm,p) -> require(pm=PNone)"marked E packet"; eh surface level (path@["packet"])v.ty p
    | EValue (snapshot,value) | EIgnored (Some(snapshot,value)) -> captures:={at;snapshot;value}::!captures; unresolved:=CaptureBinding at::!unresolved
    | EIgnored None -> ()
    | EFVar f -> unresolved:=FreeVariableBinding(at,f)::!unresolved
    | EBVar b -> unresolved:=BoundVariableScope(at,b)::!unresolved
    | EBottom -> unresolved:=BottomExpression at::!unresolved
    | EApp (f,args) -> unresolved:=ApplicationEffectAndInterface(at,f)::!unresolved;List.iteri(fun i xs -> List.iteri(fun j x -> ev surface level (path@["arg";string_of_int i;string_of_int j])x)xs)args
    | ELet (owned,pattern,bound,next) -> bindings:={at;owned;pattern}::!bindings;unresolved:=LetScope at::!unresolved;
      ev surface level (path@["let_bound"])bound;ev surface level(path@["let_next"])next
    | EJoinMarkers _ -> unsupported "unresolved E join markers"
    | EMutBorrowInput v -> child v
    | EBorrow b -> (match b with
      | EEndedIgnoredMutBorrow b -> child b.child; given b.given_back; sym surface level(path@["given_back_meta"])b.given_back_meta
      | EEndedMutBorrow (m,c) -> sym surface level(path@["given_back_meta"])m.given_back; child c
      | EMutBorrow (_,_,c) | EIgnoredMutBorrow (_,c) -> child c)
    | ELoan l -> (match l with
      | EEndedMutLoan l -> child l.child;given l.given_back; concrete surface level(path@["given_back_meta"])l.given_back_meta
      | EEndedIgnoredMutLoan l -> child l.child;given l.given_back; concrete surface level(path@["given_back_meta"])l.given_back_meta
      | EMutLoan (_,_,c) | EIgnoredMutLoan (_,c) -> child c)
  in
  List.iteri(fun i v -> av 0 ["avalue";string_of_int i]v)owner.avalues;
  (match owner.cont with None->() |Some c ->
    Option.iter(ev EOutput 0 ["output"])c.output;
    Option.iter(ev EInput 0 ["input"])c.input);
  {owner;nodes=List.rev !nodes;packets=List.rev !packets;metadata=List.rev !metadata;captures=List.rev !captures;
   concrete_metadata=List.rev !concrete_metadata;bindings=List.rev !bindings;shared_reborrows=List.rev !shared_reborrows;unresolved=List.rev !unresolved}

(** An uncommitted plan. Captures and executable E bodies remain unresolved;
    this value is deliberately not an argument accepted by any merge function. *)
type obligation =
  | UncommittedOnly
  | OrderedContinuationComposition
  | CaptureAndBinderValidation
  | RecursiveInterfaceBinding
  | EffectPreservation
  | ExternalPermissionClosure
  | ContinuationLayoutValidation

type region_pair = { left_region : RegionId.id; right_region : RegionId.id;
  is_owned : bool; is_ended : bool }

(** Full native type equality up to a bijective occurrence-preserving region
    renaming, with the same owned and ended classifications. Unlike normalized,
    this retains the distinction between multiple non-owned regions. *)
let compare_native_regions (ctx : context) (left_owner : abs) (right_owner : abs) left right =
  let canonical ty =
    let ids=ref [] in
    let v=object inherit [_] map_ty
      method! visit_region () = function
        | RVar(Free r) ->
          let rec index n = function
            | [] -> ids := !ids@[r]; n
            | x::xs -> if x=r then n else index(n+1)xs in
          RVar(Free(RegionId.of_int(index 0 !ids)))
        | _ -> unsupported "selected native type contains non-free region"
    end in let ty=v#visit_ty () ty in ty,!ids in
  let l,ls=canonical left and r,rs=canonical right in
  require(equal_ty l r && List.length ls=List.length rs)"full native region-occurrence shape mismatch";
  let rename=object inherit [_] map_ty
    method! visit_region () = function
      | RVar(Free a) -> let rec find l r=match l,r with
          | x::xs,y::ys -> if a=x then RVar(Free y)else find xs ys
          | _ -> unsupported "region correspondence not total" in find ls rs
      | _ -> unsupported "selected native type contains non-free region"
  end in
  require(equal_ty(rename#visit_ty () left)right)"full original type is not preserved by region map";
  List.map2(fun a b ->
    let owned=RegionId.Set.mem a left_owner.regions.owned
    and ended=RegionId.Set.mem a ctx.ended_regions in
    require(owned=RegionId.Set.mem b right_owner.regions.owned)"owned region correspondence mismatch";
    require(ended=RegionId.Set.mem b ctx.ended_regions)"ended ancestor correspondence mismatch";
    {left_region=a;right_region=b;is_owned=owned;is_ended=ended})ls rs

type dual_plan = {
  loan_descriptor : descriptor;
  borrow_descriptor : descriptor;
  paired : (packet * packet) list;
  region_correspondence : region_pair list;
  retained_loan_nodes : node list;
  retained_borrow_nodes : node list;
  obligations : obligation list;
}
let find_packet (d : descriptor) path =
  match List.filter(fun (p : packet) -> p.at.surface=A && p.at.path=path)d.packets with
  | [p] -> p | _ -> unsupported "candidate path is missing or ambiguous"
let active (p : packet) polarity = require(p.phase=Live && p.polarity=polarity)"wrong live polarity"
let original_ap (p : packet) = match p.at.original with APacket p->p |_->unsupported "not A packet"
let prefix a b = let rec f a b=match a,b with [],_->true|x::xs,y::ys when x=y->f xs ys|_->false in f a b
let plan_dual (ctx : context) ~fixed_aids ~(loan_owner : abs) ~loan_path ~(borrow_owner : abs) ~borrow_path =
  require(loan_owner.abs_id<>borrow_owner.abs_id)"identical owners";
  List.iter(fun a -> require(a.can_end && not(AbsId.Set.mem a.abs_id fixed_aids))"fixed/non-endable owner") [loan_owner;borrow_owner];
  let ld=describe_owner ctx loan_owner and bd=describe_owner ctx borrow_owner in
  let l=find_packet ld loan_path and b=find_packet bd borrow_path in
  active l Loan;active b Borrow;
  require(l.at.level=0 && b.at.level=0)"parent packet is not level zero";
  require(l.sid=b.sid)"parent SID mismatch";
  require(equal_ty l.typ.normalized b.typ.normalized)"parent owned projection mismatch";
  let region_correspondence=compare_native_regions ctx loan_owner borrow_owner l.typ.full b.typ.full in
  let lm,bm = match original_ap l, original_ap b with
    | AProjLoans {consumed=[];borrows=[m,AProjBorrows {loans=[];_}];_},
      AProjBorrows {loans=[n,AProjLoans {consumed=[];borrows=[];_}];_}->m,n
    | _ -> unsupported "expected one reciprocal child and no consumed/extra history" in
  let lc=find_packet ld (loan_path@["borrows";"0";"child"])
  and bc=find_packet bd (borrow_path@["loans";"0";"child"]) in
  active lc Borrow;active bc Loan;
  require(lc.at.level=1 && bc.at.level=1)"child level mismatch";
  require(lc.sid=bc.sid && lc.sid<>l.sid)"child SID mismatch or same parent SID";
  require(equal_ty lc.typ.normalized bc.typ.normalized)"child owned projection mismatch";
  require(Some lm.sv_id=lc.sid && Some bm.sv_id=bc.sid)"history metadata SID mismatch";
  (* Original instantiations may differ across owners. The loan-owner history
     records the borrow-owner's newly returned value, not the active old type. *)
  require(equal_ty lm.proj_ty bc.typ.full && equal_ty bm.proj_ty bc.typ.full)"history metadata full type mismatch";
  require(equal_ty l.typ.full lc.typ.full && equal_ty b.typ.full bc.typ.full)"unexpected per-owner type change";
  let selected=[loan_owner,l;loan_owner,lc;borrow_owner,b;borrow_owner,bc] in
  List.iter(fun (owner,(p : packet)) ->
    require(p.type_origin=ProjectorType)"selected packet has only inherited type evidence";
    require(not p.typ.owned_mutable)"mutable owned projection unsupported by dual planner";
    require(not(AbsLevelSet.mem p.at.level owner.ended_subabs))"selected level recorded ended";
    require(RegionId.Set.is_empty(RegionId.Set.inter owner.regions.owned ctx.ended_regions))"selected owned region ended";
    (* An earlier concrete merge may retain unrelated owned regions. Only
       regions visible in this packet participate in its projection; the full
       native correspondence above compares their ownership pointwise. Keep
       the complete owner set for retained-node and union-mask checks. *)
    let selected_owned=RegionId.Set.inter owner.regions.owned p.typ.free_regions in
    require(not(RegionId.Set.is_empty selected_owned))"selected packet has no owned region";
    let check = object
      inherit [_] iter_ty
      method! visit_region () = function
        | RVar(Free _) -> ()
        | _ -> unsupported "selected native type contains non-free region"
    end in check#visit_ty () p.typ.full) selected;
  let unique (d : descriptor) (p : packet) =
    require(not(List.exists(fun(r:shared_reborrow)->match r.proj with Some x->Some x.sv_id=p.sid|None->false)d.shared_reborrows))"selected SID has additional shared reborrow occurrence";
    require(List.length(List.filter(fun (q : packet)->q.at.surface=A && q.phase=Live && q.sid=p.sid)d.packets)=1)"duplicate live SID occurrence in owner" in
  List.iter(unique ld)[l;lc];List.iter(unique bd)[b;bc];
  (* Exclude only selected packet subtrees from the residual VIEW. Owners,
     enclosing wrappers, E nodes, metadata and captures stay original objects. *)
  let residual d path = List.filter(fun n->n.surface<>A || not(prefix path n.path))d.nodes in
  {loan_descriptor=ld;borrow_descriptor=bd;paired=[l,b;lc,bc];region_correspondence;
   retained_loan_nodes=residual ld loan_path;retained_borrow_nodes=residual bd borrow_path;
   obligations=[UncommittedOnly;OrderedContinuationComposition;CaptureAndBinderValidation;
    RecursiveInterfaceBinding;EffectPreservation;ExternalPermissionClosure;ContinuationLayoutValidation]}
