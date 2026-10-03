(** Only two admitted native nominal instances; never a generic Zip model.
    The abstract token proves only the entrypoint's pinned-input checks, not
    unsafe specialization, allocation, callback destruction or Drop refinement. *)
open Types
open LlbcAst
open AppliedBuiltins
let ( let* ) = Option.bind

type orientation = SliceVec | VecSlice
let enabled () = Option.is_some (MixedZipAdmission.token ()) && Config.backend () = Config.Lean

type shape = U8 | U32 | Bool | Vec of shape | Opt of shape | User of string
let user_path = function
  | "Name" -> ["minimal_smt"; "smtlib_names"; "Name"]
  | ("FreeSortId" | "ResolvedSort" | "FunctionSignature" | "DeclarationKind") as n ->
      ["minimal_smt"; "smtlib_signatures"; n]
  | n -> ["minimal_smt"; "smtlib_model"; n]
let local_path meta names = meta.is_local && path {meta with is_local = false} names
let empty_args args = args = TypesUtils.empty_generic_args
let u32 = TScalar (TInteger (Unsigned U32))

let rec has_shape crate ty shape =
  match shape, ty with
  | U8, TScalar (TInteger (Unsigned U8))
  | U32, TScalar (TInteger (Unsigned U32))
  | Bool, TScalar TBool -> true
  | (Vec element | Opt element), TAdt {id; builtin = None; generics = {regions = []; types = [t]; const_generics = []; trait_refs = []}} ->
      (match TypeDeclId.Map.find_opt id crate.type_decls with
      | Some d -> path d.item_meta (match shape with Vec _ -> ["alloc"; "vec"; "Vec"] | _ -> ["core"; "option"; "Option"])
          && has_shape crate t element
      | None -> false)
  | User n, TAdt {id; builtin = None; generics} when empty_args generics ->
      (match TypeDeclId.Map.find_opt id crate.type_decls with
      | Some d when local_path d.item_meta (user_path n)
          && d.generics = TypesUtils.empty_generic_params && d.src = NormalType ->
          let fields actual expected = List.length actual = List.length expected &&
            List.for_all2 (fun (f : field) (name, positional, ty) ->
              f.field_name = name && f.is_positional = positional && has_shape crate f.field_ty ty) actual expected in
          let variants actual expected = List.length actual = List.length expected &&
            List.for_all2 (fun (v : variant) (name, fs) -> v.variant_name = name && fields v.fields fs) actual expected in
          (match n, d.kind with
          | "Name", Struct fs -> fields fs ["bytes",false,Vec U8]
          | "FreeSortId", Struct fs -> fields fs ["_0",true,U32]
          | "ResolvedSort", Enum vs -> variants vs ["Bool",[]; "Free",["_0",true,User "FreeSortId"]]
          | "DeclarationKind", Enum vs -> variants vs ["Function",[]; "Constant",[]]
          | "FunctionSignature", Struct fs -> fields fs ["name",false,User "Name"; "domain",false,Vec (User "ResolvedSort"); "range",false,User "ResolvedSort"; "kind",false,User "DeclarationKind"]
          | "ModelValue", Enum vs -> variants vs ["Boolean",["_0",true,Bool]; "Element",["sort",false,User "FreeSortId"; "index",false,U32]]
          | "ValidatedRow", Struct fs -> fields fs ["arguments",false,Vec (User "ModelValue"); "result",false,User "ModelValue"]
          | "ValidatedTable", Struct fs -> fields fs ["rows",false,Vec (User "ValidatedRow"); "default",false,User "ModelValue"]
          | _ -> false)
      | _ -> false)
  | _ -> false

let global_allocator crate = function
  | TAdt {id; builtin = None; generics} when empty_args generics ->
      (match TypeDeclId.Map.find_opt id crate.type_decls with
      | Some d -> path d.item_meta ["alloc"; "alloc"; "Global"]
      | None -> false)
  | _ -> false

let vec_iterator crate = function
  | TAdt {id; builtin = None; generics = {regions = []; types = [element; allocator]; const_generics = []; trait_refs = []}} ->
      let* d = TypeDeclId.Map.find_opt id crate.type_decls in
      if path d.item_meta ["alloc"; "vec"; "into_iter"; "IntoIter"] && global_allocator crate allocator
      then Some element else None
  | _ -> None

let vec_witness crate iter item witness =
  let* witness = resolve_parent crate [] witness in
  match witness.kind with
  | TraitImpl r ->
      let* (d, _, expected) = instantiate_impl crate r in
      if not (impl_path d.item_meta ["alloc"; "vec"; "into_iter"] d.def_id)
         || not (iterator_trait crate expected.id) || expected <> witness.trait_decl_ref.binder_value then None else
      (match expected.generics with
      | {regions = []; types = [self; actual]; const_generics = []; trait_refs = []}
        when self = iter && actual = item -> Some ()
      | _ -> None)
  | _ -> None

let classify_trait crate original =
  let* _admission = MixedZipAdmission.token () in
  if not (enabled ()) then None else
  let* tr = resolve_parent crate [] original in
  match tr.kind with
  | TraitImpl r ->
      let* (d, _, expected) = instantiate_impl crate r in
      if not (impl_path d.item_meta ["core"; "iter"; "adapters"; "zip"] d.def_id)
         || not (iterator_trait crate expected.id) || expected <> tr.trait_decl_ref.binder_value then None else
      (match r.generics with
      | {regions = []; types = [a; b; item_a; item_b]; const_generics = []; trait_refs = [ia; ib]} ->
          (match slice_iterator crate a, vec_iterator crate b with
          | Some (ra, ta), Some tb when shared_item ra ta item_a && item_b = tb
              && has_shape crate ta (User "Name") && tb = u32 ->
              let* () = slice_witness crate a item_a ia in
              let* () = vec_witness crate b item_b ib in Some (SliceVec, ta, tb)
          | _ ->
              let* ta = vec_iterator crate a in
              let* (rb, tb) = slice_iterator crate b in
              if item_a <> ta || not (shared_item rb tb item_b)
                 || not (has_shape crate ta (Opt (User "ValidatedTable")) && has_shape crate tb (User "FunctionSignature")) then None else
              let* () = vec_witness crate a item_a ia in
              let* () = slice_witness crate b item_b ib in Some (VecSlice, ta, tb))
      | _ -> None)
  | _ -> None

let classify_function crate id generics =
  if not (enabled ()) then None else
  let* f = FunDeclId.Map.find_opt id crate.fun_decls in
  if f.item_meta.is_local || not (args_fit f.generics generics) then None else
  match f.src with
  | TraitImplFun (impl, decl, method_id, _) ->
      let subst = Charon.Substitute.make_subst_from_generics f.generics generics Self in
      let impl = Charon.Substitute.st_substitute_visitor#visit_trait_impl_ref subst impl in
      let decl = Charon.Substitute.trait_decl_ref_substitute subst decl in
      let tr = {kind = TraitImpl impl; trait_decl_ref = {binder_regions = []; binder_value = decl}} in
      let* (orientation, ta, tb) = classify_trait crate tr in
      let* tdecl = TraitDeclId.Map.find_opt decl.id crate.trait_decls in
      let* meth = TraitMethodId.Map.find_opt method_id tdecl.methods in
      (match meth.binder_value.name, generics.types, generics.trait_refs with
      | "next", [_; _; _; _], [_; _]
        when List.length generics.regions = 1 && generics.const_generics = [] ->
          Some ((orientation, Next), {TypesUtils.empty_generic_args with types = [ta; tb]})
      | "fold", [_; _; acc; closure; _; _], [_; _; fnmut]
        when generics.regions = [] && generics.const_generics = [] ->
          Some ((orientation, Fold), {TypesUtils.empty_generic_args with types = [ta; tb; acc; closure]; trait_refs = [fnmut]})
      | _ -> None)
  | _ -> None
