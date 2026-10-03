(** Experimental per-use library bindings. Original concrete witnesses are
    checked before region erasure; uncertain evidence means no selection. *)
open Types
open LlbcAst

let enabled () = !Config.applied_slice_zip && Config.backend () = Config.Lean
let ( let* ) = Option.bind

let path (meta : item_meta) names =
  not meta.is_local && List.length meta.name = List.length names
  && List.for_all2 (fun elem name -> match elem with
    | PeIdent (s, dis) -> s = name && Disambiguator.to_int dis = 0
    | _ -> false) meta.name names

let impl_path (meta : item_meta) names id =
  match List.rev meta.name with
  | PeImpl (ImplElemTrait actual) :: prefix ->
      actual = id && path {meta with name = List.rev prefix} names
  | _ -> false

let iterator_trait crate id =
  match TraitDeclId.Map.find_opt id crate.trait_decls with
  | Some d -> path d.item_meta ["core"; "iter"; "traits"; "iterator"; "Iterator"]
  | None -> false

let args_fit (params : generic_params) (args : generic_args) =
  List.length params.regions = List.length args.regions
  && List.length params.types = List.length args.types
  && List.length params.const_generics = List.length args.const_generics
  && List.length params.trait_clauses = List.length args.trait_refs

let instantiate_impl crate (r : trait_impl_ref) =
  let* d = TraitImplId.Map.find_opt r.id crate.trait_impls in
  if not (args_fit d.generics r.generics) then None else
  let subst = Charon.Substitute.make_subst_from_generics d.generics r.generics (TraitImpl r) in
  Some (d, subst, Charon.Substitute.trait_decl_ref_substitute subst d.impl_trait)

(** Resolve the original instantiated implied refs. Do not guess from a
    projection's advertised trait name. Higher-ranked/cyclic refs stay opaque. *)
let rec resolve_parent crate seen (tr : trait_ref) : trait_ref option =
  if List.exists (fun x -> x = tr) seen || tr.trait_decl_ref.binder_regions <> [] then None
  else match tr.kind with
  | ParentClause (parent, id) ->
      let* parent = resolve_parent crate (tr :: seen) parent in
      (match parent.kind with
      | TraitImpl impl ->
          let* (d, subst, expected) = instantiate_impl crate impl in
          if expected <> parent.trait_decl_ref.binder_value then None else
          let* original = List.nth_opt d.implied_trait_refs (TraitClauseId.to_int id) in
          let resolved = Charon.Substitute.trait_ref_substitute subst original in
          if resolved.trait_decl_ref <> tr.trait_decl_ref then None
          else resolve_parent crate (tr :: seen) resolved
      | _ -> None)
  | _ -> Some tr

let slice_iterator crate ty = match ty with
  | TAdt {id; builtin = None; generics = {regions = [region]; types = [element]; const_generics = []; trait_refs = []}} ->
      let* d = TypeDeclId.Map.find_opt id crate.type_decls in
      if path d.item_meta ["core"; "slice"; "iter"; "Iter"] then Some (region, element) else None
  | _ -> None

let shared_item region element item = match item with
  | TRef (r, t, RShared) -> r = region && t = element
  | _ -> false

let slice_witness crate iter item (witness : trait_ref) =
  let* witness = resolve_parent crate [] witness in
  match witness.kind with
  | TraitImpl r ->
      let* (d, _, expected) = instantiate_impl crate r in
      if not (impl_path d.item_meta ["core"; "slice"; "iter"] d.def_id)
         || not (iterator_trait crate expected.id)
         || expected <> witness.trait_decl_ref.binder_value then None else
      (match expected.generics with
      | { regions = []; types = [self; actual]; const_generics = []; trait_refs = [] }
        when self = iter && actual = item -> Some ()
      | _ -> None)
  | _ -> None

let classify_trait crate (original : trait_ref) =
  if not (enabled ()) then None else
  let* tr = resolve_parent crate [] original in
  match tr.kind with
  | TraitImpl r ->
      let* (d, _, expected) = instantiate_impl crate r in
      if not (impl_path d.item_meta ["core"; "iter"; "adapters"; "zip"] d.def_id)
         || not (iterator_trait crate expected.id)
         || expected <> tr.trait_decl_ref.binder_value then None else
      (match r.generics with
      | {regions = []; types = [a; b; item_a; item_b]; const_generics = []; trait_refs = [ia; ib]} ->
          let* (ra, ta) = slice_iterator crate a in
          let* (rb, tb) = slice_iterator crate b in
          if not (shared_item ra ta item_a && shared_item rb tb item_b) then None else
          let* () = slice_witness crate a item_a ia in
          let* () = slice_witness crate b item_b ib in
          Some (ta, tb)
      | _ -> None)
  | _ -> None

type method_binding = Next | Fold

let classify_function crate id (generics : generic_args) =
  if not (enabled ()) then None else
  let* f = FunDeclId.Map.find_opt id crate.fun_decls in
  if f.item_meta.is_local || not (args_fit f.generics generics) then None else
  match f.src with
  | TraitImplFun (impl, decl, method_id, _) ->
      let subst = Charon.Substitute.make_subst_from_generics f.generics generics Self in
      let impl = Charon.Substitute.st_substitute_visitor#visit_trait_impl_ref subst impl in
      let decl = Charon.Substitute.trait_decl_ref_substitute subst decl in
      let tr = {kind = TraitImpl impl; trait_decl_ref = {binder_regions = []; binder_value = decl}} in
      let* (ta, tb) = classify_trait crate tr in
      let* tdecl = TraitDeclId.Map.find_opt decl.id crate.trait_decls in
      let* meth = TraitMethodId.Map.find_opt method_id tdecl.methods in
      (match meth.binder_value.name, generics.types, generics.trait_refs with
      | "next", [_; _; _; _], [_; _] when List.length generics.regions = 1 && generics.const_generics = [] ->
          Some (Next, {TypesUtils.empty_generic_args with types = [ta; tb]})
      | "fold", [_; _; acc; closure; _; _], [_; _; fnmut]
        when generics.regions = [] && generics.const_generics = [] ->
          Some (Fold, {TypesUtils.empty_generic_args with types = [ta; tb; acc; closure]; trait_refs = [fnmut]})
      | _ -> None)
  | _ -> None

(** The held library has a generic Zip.next entry. The opt-in concrete prototype
    must not accidentally admit that broader route when concrete recognition
    fails. This guard changes no registry entry and selects no fallback. *)
let is_zip_iterator_method crate id =
  match FunDeclId.Map.find_opt id crate.fun_decls with
  | Some {src = TraitImplFun (impl, decl, _, _); _} ->
      iterator_trait crate decl.id &&
      (match TraitImplId.Map.find_opt impl.id crate.trait_impls with
       | Some d -> impl_path d.item_meta ["core"; "iter"; "adapters"; "zip"] d.def_id
       | None -> false)
  | _ -> false

let classify_function_checked span crate id generics =
  let selected = classify_function crate id generics in
  if enabled () && is_zip_iterator_method crate id && Option.is_none selected then
    [%craise_opt_span] span
      "Unsupported applied Zip method: expected exact shared SliceIter witnesses and supported method/ABI";
  selected
