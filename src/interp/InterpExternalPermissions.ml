(** Read-only selected-packet external permissions. Not a cancellation API.
    The caller's immutable native declaration/analysis universe must be valid;
    the actual consumer pins a privately captured complete interpreter env. *)
open Types
open Values
module P = InterpPacketInterface
exception Unsupported of string
let reject message=raise(Unsupported message)
let require b message=if not b then reject message
let id_name (d:type_decl)=String.concat "::" (List.filter_map(function PeIdent(x,_)->Some x|_->None)d.item_meta.name)

(** Guard every type field skipped by the native positional comparison before
    inspecting region masks. No normalized type is used for admission. *)
let equal_info (a:TypesAnalysis.type_decl_info) (b:TypesAnalysis.type_decl_info) =
  a.borrows_info=b.borrows_info && a.param_infos=b.param_infos
  && a.is_tuple_struct=b.is_tuple_struct && a.has_regions=b.has_regions
  && RegionId.Set.equal a.mut_regions b.mut_regions && a.is_rec=b.is_rec

let supported_opaque decl = match id_name decl with
  | "alloc::vec::Vec" ->
      (* The canonical allocator-free Vec<T> already has the standard backend
         model. Do not extend this boundary to arbitrary opaque containers. *)
      not decl.item_meta.is_local && decl.item_meta.diagnostic_item=Some "Vec"
      && decl.generics.regions=[] && List.length decl.generics.types=1
      && decl.generics.const_generics=[] && decl.generics.trait_clauses=[]
      && decl.generics.regions_outlive=[] && decl.generics.types_outlive=[]
      && decl.generics.trait_type_constraints=[]
  | "core::iter::adapters::enumerate::Enumerate" ->
      List.length decl.generics.regions=0 && List.length decl.generics.types=1
      && decl.generics.const_generics=[]
  | "core::iter::adapters::zip::Zip" ->
      List.length decl.generics.regions=0 && List.length decl.generics.types=2
      && decl.generics.const_generics=[]
  | "core::slice::iter::Iter" ->
      List.length decl.generics.regions=1 && List.length decl.generics.types=1
      && decl.generics.const_generics=[]
  | _ -> false

(** [native_type_ctx] is independently loaded and analyzed from the exact pinned
    LLBC. Full declaration/analysis agreement is source identity, not a proof of
    native/library correspondence. The runner binds that input and the snapshot. *)
let projection_shape ~(native_type_ctx:Contexts.type_ctx) (ctx:P.context) ty =
  let rids=ref [] in
  let region = function RVar(Free r)->rids:=r::!rids
    | _ -> reject "non-free/erased/static/bound/body region" in
  let constant (c:constant_expr)= match c.kind,c.ty with
    | CInteger(UnsignedInteger(Usize,_)),TScalar(TInteger(Unsigned Usize))->()
    | _ -> reject "unsupported const generic or array length" in
  let rec visit = function
    | TScalar _ -> ()
    | TRef(r,t,_)->region r;visit t
    | TSlice(t,None)->visit t
    | TSlice(_,Some _)->reject "hidden Slice Sized witness"
    | TArray(t,n,None)->constant n;visit t
    | TArray(_,_,Some _)->reject "hidden Array Sized witness"
    | TAdt ({builtin=Some TTuple;_} as tuple) ->
        (* Tuples carry only their ordered element types. Check the complete
           native constructor so no region, const or trait witness is skipped. *)
        require (equal_ty (TAdt tuple) (TypesUtils.mk_tuple_ty tuple.generics.types))
          "noncanonical builtin tuple type";
        List.iter visit tuple.generics.types
    | TAdt d ->
        require(d.builtin=None)"builtin ADT tag outside nominal fragment";
        require(d.generics.trait_refs=[])"hidden ADT trait witness";
        let decl=match TypeDeclId.Map.find_opt d.id ctx.type_ctx.type_decls with
          | Some x->x|None->reject "unknown nominal declaration"in
        require(decl.def_id=d.id)"inconsistent nominal declaration id";
        let native_decl=match TypeDeclId.Map.find_opt d.id native_type_ctx.type_decls with
          |Some x->x|None->reject "nominal declaration absent from pinned native universe"in
        require(Types.equal_type_decl decl native_decl)"full declaration differs from pinned native universe";
        require(decl.src=NormalType)"closure/vtable/synthetic type source unsupported";
        (match decl.kind with Struct _|Enum _->()|Opaque when supported_opaque decl->()
         | Opaque->reject("unrecognized opaque nominal type: " ^ id_name decl)|_->reject"alias/union/error declaration unsupported");
        let info=match TypeDeclId.Map.find_opt d.id ctx.type_ctx.type_infos with
          | Some x->x|None->reject "missing nominal type analysis"in
        let native_info=match TypeDeclId.Map.find_opt d.id native_type_ctx.type_infos with
          |Some x->x|None->reject "analysis absent from pinned native universe"in
        require(equal_info info native_info)"full analysis differs from pinned native universe";
        if decl.kind=Opaque && id_name decl="alloc::vec::Vec" then begin
          (* Region permissions occur in T's visible positions; Vec itself has
             no hidden borrowed region and does not wrap T in a borrow. This
             matches TypesAnalysis and the registered ordinary Vec model. *)
          require(info.borrows_info=TypesAnalysis.type_borrows_info_init
            && not info.has_regions && RegionId.Set.is_empty info.mut_regions
            && match info.param_infos with
               | [parameter] -> not(parameter.under_borrow || parameter.under_mut_borrow)
               | _ -> false)
            "canonical Vec has unexpected native borrow/parameter analysis"
        end;
        require(not info.borrows_info.contains_static)"nominal type contains static borrow";
        require(List.length d.generics.regions=List.length decl.generics.regions
          &&List.length d.generics.types=List.length decl.generics.types
          &&List.length d.generics.const_generics=List.length decl.generics.const_generics)
          "nominal generic arity mismatch";
        require(List.length info.param_infos=List.length decl.generics.types)"inconsistent analysis parameter arity";
        List.iter constant d.generics.const_generics;
        List.iter region d.generics.regions;List.iter visit d.generics.types
    | _->reject "unsupported type constructor (variable/projection/function/dyn/raw/metadata/never/pattern/error)" in
  visit ty;
  let rename=object inherit [_] map_ty method! visit_region () = function
    | RVar(Free _)->RVar(Free(RegionId.of_int 0))
    | _->reject "non-free region outside admitted visible type positions"end in
  rename#visit_ty () ty,List.rev !rids

let intersects ~native_type_ctx (ctx:P.context) left_owned left_ty right_owned right_ty =
  let l,ls=projection_shape ~native_type_ctx ctx left_ty and r,rs=projection_shape ~native_type_ctx ctx right_ty in
  require(equal_ty l r)"complete positional type shape mismatch";
  require(List.length ls=List.length rs)"region-position length mismatch";
  List.exists2(fun a b->RegionId.Set.mem a left_owned&&RegionId.Set.mem b right_owned)ls rs

type origin = Packet of aproj | Reborrow of abstract_shared_borrow
type occurrence = { owner:abs; path:P.path; level:int; polarity:P.polarity;
  marker:proj_marker; sid:symbolic_value_id; ty:ty; origin:origin }
type runtime = { path:string; value:tvalue; symbolic:symbolic_value }
type comparison = { selected:occurrence; external_permission:occurrence;
  intersects:bool option; reason:string option }
type report = {
  plan:P.dual_plan option;
  current_env:env;
  owners:abs list;
  selected:occurrence list;
  external_permissions:occurrence list;
  comparisons:comparison list;
  runtime_dependencies:runtime list;
  issues:string list;
  closed_in_supplied_current_environment:bool;
}

let inventory ?shared_lookup ?shared_values_lookup span env selected_sids =
  let lookup marker bid = match shared_values_lookup,shared_lookup with
    | Some lookup,_ -> lookup marker bid
    | None,Some lookup -> [marker,lookup marker bid]
    | None,None -> [marker,InterpBorrowsCore.lookup_shared_value span env bid] in
  let branch_path path = function
    | PNone -> path | PLeft -> path^"/left" | PRight -> path^"/right" in
  let permissions=ref [] and runtime=ref [] and issues=ref [] in
  let problem x=issues:=x::!issues in
  let rec concrete marker ancestors bids path (v:tvalue) =
    if List.exists(fun x->x==v)ancestors then problem(path^": cyclic current concrete carrier")
    else let ancestors=v::ancestors in
    match v.value with
    | VSymbolic s -> if SymbolicValueId.Set.mem s.sv_id selected_sids then
        runtime:={path;value=v;symbolic=s}::!runtime
    | VLiteral _|VBottom|VLoan(VMutLoan _)->()
    | VAdt a->List.iteri(fun i v->concrete marker ancestors bids(path^"/field["^string_of_int i^"]")v)a.fields
    | VBorrow(VMutBorrow(_,v))|VLoan(VSharedLoan(_,v))->concrete marker ancestors bids(path^"/payload")v
    | VBorrow(VSharedBorrow(bid,_)|VReservedMutBorrow(bid,_))->
        if BorrowId.Set.mem bid bids then problem(path^": cyclic shared-borrow lookup")
        else (try
          List.iter (fun (branch,value) ->
            concrete branch ancestors (BorrowId.Set.add bid bids)
              (branch_path (path^"/shared_payload") branch) value) (lookup marker bid)
        with exn->problem(path^": unresolved shared borrow: "^Printexc.to_string exn))in
  let rec packet owner path level marker p =
    let add polarity sid ty=permissions:={owner;path;level;polarity;marker;sid;ty;origin=Packet p}::!permissions in
    let history channel xs=List.iteri(fun i (_,p)->packet owner(path@[channel;string_of_int i;"child"])(level+1)marker p)xs in
    match p with
    | AProjLoans q->add P.Loan q.proj.sv_id q.proj.proj_ty;history"consumed"q.consumed;history"borrows"q.borrows
    | AProjBorrows q->add P.Borrow q.proj.sv_id q.proj.proj_ty;history"loans"q.loans
    | AEndedProjLoans q->history"consumed"q.consumed;history"borrows"q.borrows
    | AEndedProjBorrows q->history"loans"q.loans
    | AEmpty->()
  and av owner path level (v:tavalue) =
    let child x=av owner(path@["child"])level x and given x=av owner(path@["given_back"])(level+1)x in
    let shared marker v=concrete marker [] BorrowId.Set.empty("owner"^AbsId.to_string owner.abs_id^"/"^String.concat"/"path^"/shared_value")v in
    match v.value with
    | ASymbolic(pm,p)->packet owner(path@["packet"])level pm p
    | AAdt a->List.iteri(fun i v->av owner(path@["field";string_of_int i])level v)a.fields
    | AIgnored _->()
    | ALoan q->(match q with
      | AMutLoan(_,_,x)|AIgnoredMutLoan(_,x)|AIgnoredSharedLoan x->child x
      | ASharedLoan(marker,_,v,x)->shared marker v;child x
      | AEndedSharedLoan(v,x)->shared PNone v;child x
      | AEndedMutLoan q->given q.given_back;child q.child
      | AEndedIgnoredMutLoan q->given q.given_back;child q.child)
    | ABorrow q->(match q with
      | AMutBorrow(_,_,x)|AIgnoredMutBorrow(_,x)|AEndedMutBorrow(_,x)->child x
      | AEndedIgnoredMutBorrow q->child q.child;given q.given_back
      | ASharedBorrow(marker,bid,_)->
          (* Follow the original loan rather than treating a retained concrete
             borrow as absence of a selected symbolic runtime dependency. *)
          let path="owner"^AbsId.to_string owner.abs_id^"/"^String.concat"/"path^"/shared_borrow"in
          (try
            List.iter (fun (branch,value) ->
              concrete branch [] (BorrowId.Set.singleton bid) (branch_path path branch) value)
              (lookup marker bid)
          with exn->problem(path^": unresolved shared borrow: "^Printexc.to_string exn))
      | AEndedSharedBorrow->()
      | AProjSharedBorrow xs->List.iteri(fun i x->match x with
        | AsbBorrow _->()
        | AsbProjReborrows p->permissions:={owner;path=path@["shared_reborrow";string_of_int i];level;polarity=P.Borrow;marker=PNone;sid=p.sv_id;ty=p.proj_ty;origin=Reborrow x}::!permissions)xs)in
  List.iteri(fun i->function
    | EFrame->()
    | EBinding(_,v)->concrete PNone [] BorrowId.Set.empty("binding["^string_of_int i^"]")v
    | EAbs owner->List.iteri(fun i v->av owner["avalue";string_of_int i]0 v)owner.avalues)env;
  List.rev !permissions,List.rev !runtime,List.rev !issues

let check ?(allow_marked=false) span ~native_type_ctx (ctx:P.context) ~current_env ~supplied_env ~fixed_aids
    ~loan_owner ~loan_path ~borrow_owner ~borrow_path =
  let owners=List.filter_map(function EAbs a->Some a|_->None)supplied_env in
  let empty issue={plan=None;current_env=supplied_env;owners;selected=[];external_permissions=[];
    comparisons=[];runtime_dependencies=[];issues=[issue];closed_in_supplied_current_environment=false}in
  try
    require(current_env==supplied_env)"IncompleteEnvironment: supplied list is not the recorded current environment";
    let unique=List.fold_left(fun ids a->require(not(AbsId.Set.mem a.abs_id ids))"duplicate current owner id";AbsId.Set.add a.abs_id ids)AbsId.Set.empty owners in
    ignore unique;
    List.iter(fun a->require(List.exists(fun x->x==a)owners)"selected owner not the original current object")[loan_owner;borrow_owner];
    let plan=P.plan_dual ~allow_marked ctx ~fixed_aids ~loan_owner ~loan_path ~borrow_owner ~borrow_path in
    let packet_sids=List.fold_left(fun ids(l,r)->List.fold_left(fun ids(p:P.packet)->match p.sid with
      |Some s->SymbolicValueId.Set.add s ids|None->reject"selected packet has no SID")ids[l;r])SymbolicValueId.Set.empty plan.paired in
    let shared_values_lookup = if allow_marked then Some
      (InterpSharedPacketSignature.lookup_retained_shared_values_for_inventory_in_env span
        ~type_infos:native_type_ctx.Contexts.type_infos ~ended_regions:ctx.ended_regions supplied_env) else None in
    let all,runtime,inventory_issues=inventory ?shared_values_lookup span supplied_env packet_sids in
    let expected=List.concat_map(fun(l,r)->[loan_owner,l;borrow_owner,r])plan.paired in
    let selected=List.map(fun(owner,(p:P.packet))->
      let candidates=List.filter(fun o->o.owner==owner&&o.path=p.at.path&&o.level=p.at.level)all in
      match candidates,p.at.original with
      | [o],P.APacket original ->
          require(p.at.surface=P.A&&p.phase=P.Live&&o.polarity=p.polarity&&Some o.sid=p.sid
            &&o.marker=p.marker&&equal_ty o.ty p.typ.full)"selected packet fields disagree";
          (match o.origin with Packet actual->require(actual==original)"selected packet identity mismatch"|_->reject"selected shared reborrow");o
      |_->reject"selected path missing/ambiguous/not an actual packet")expected in
    List.iter(fun o->ignore(projection_shape ~native_type_ctx ctx o.ty))selected;
    let external_permissions=List.filter(fun o->SymbolicValueId.Set.mem o.sid packet_sids
      &&not(List.exists(fun s->s==o)selected))all in
    let issues=ref inventory_issues in
    List.iter(fun r->issues:= !issues@[r.path^": current concrete symbolic runtime dependency"])runtime;
    let comparisons=List.concat_map(fun selected->List.filter_map(fun external_permission->
      if selected.sid<>external_permission.sid then None else
      let answer=try
        let opposite_branch = allow_marked && match selected.marker,external_permission.marker with
          | PLeft,PRight | PRight,PLeft -> true
          | _ -> false in
        require(external_permission.marker=PNone
          || (allow_marked && external_permission.marker=selected.marker)
          || opposite_branch)"unsupported external projection marker";
        require(not(AbsLevelSet.mem external_permission.level external_permission.owner.ended_subabs))"active projector in ended sublevel";
        require(RegionId.Set.is_empty(RegionId.Set.inter external_permission.owner.regions.owned ctx.ended_regions))"active external owner region ended";
        let mask_overlap=intersects ~native_type_ctx ctx selected.owner.regions.owned selected.ty
          external_permission.owner.regions.owned external_permission.ty in
        (* During a join the marker is part of permission identity. Opposite
           branch copies remain in the complete inventory and retain all
           original type/liveness checks; they cannot alias this branch's
           cancellation. Unmarked and same-side occurrences remain blockers. *)
        let overlap=mask_overlap && not opposite_branch in
        if overlap then issues:= !issues@["overlapping external permission: owner"^AbsId.to_string external_permission.owner.abs_id^"/"^String.concat"/"external_permission.path];
        {selected;external_permission;intersects=Some overlap;reason=None}
      with Unsupported reason->issues:= !issues@[reason];{selected;external_permission;intersects=None;reason=Some reason}in Some answer)external_permissions)selected in
    {plan=Some plan;current_env=supplied_env;owners;selected;external_permissions;comparisons;
      runtime_dependencies=runtime;issues= !issues;closed_in_supplied_current_environment= !issues=[]}
  with Unsupported s->empty s|Errors.CFailure e->empty("plan rejected: "^e.msg)|Errors.RFailure->empty"plan rejected by native invariant guard"
