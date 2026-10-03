(** Conservative live-use closure after applied binding selection. Only
    extraction reachability changes; source declarations/bodies stay intact. *)
open Types
open LlbcAst
open LlbcAstUtils

(** Opt-in prototype: compute emission dependencies after the existing builtin
    argument filters. This does not rewrite source types or calls. In particular,
    a directly called hash method remains live; only dictionary/type arguments
    explicitly erased by a backend binding cease to be dependency edges. *)
let builtin_pruning_enabled () =
  Sys.getenv_opt "AENEAS_EXPERIMENTAL_BUILTIN_PRUNING" = Some "1"

let filter_kept span what keep values =
  match keep with
  | None -> values
  | Some keep ->
      [%cassert] span (List.length keep = List.length values)
        ("Ill-formed builtin " ^ what ^ " filter during dependency pruning");
      List.filter_map (fun (keep, value) -> if keep then Some value else None)
        (List.combine keep values)

let filtered_args span keep_params keep_trait_clauses (args : generic_args) =
  {args with
    types = filter_kept span "type argument" keep_params args.types;
    trait_refs = filter_kept span "trait argument" keep_trait_clauses args.trait_refs}

let filtered_params span keep_params keep_trait_clauses (params : generic_params) =
  {params with
    types = filter_kept span "type parameter" keep_params params.types;
    trait_clauses = filter_kept span "trait clause" keep_trait_clauses params.trait_clauses}

let prune (crate : crate) =
  let builtin_pruning = builtin_pruning_enabled () in
  if not (AppliedZipDispatch.enabled () || builtin_pruning) then crate else (
  [%cassert_opt_span] None (Config.backend () = Config.Lean)
    "Experimental builtin dependency pruning is available only with Lean";
  [%cassert_opt_span] None !Config.filter_trait_impl_methods
    "Experimental builtin dependency pruning requires the supported trait-method subset";
  let groups = [%silent_unwrap_opt_span] None crate.declarations in
  let eligible = List.fold_left (fun acc g ->
    List.fold_left (fun acc id -> AnyDeclIdSet.add id acc) acc
      (Charon.GAstUtils.declaration_group_to_list g)) AnyDeclIdSet.empty groups in
  let name_ctx = Charon.NameMatcher.ctx_from_crate crate in
  let modeled_meta (m : item_meta) = not m.is_local && not m.started_from in
  let function_info (f : fun_decl) =
    if not (modeled_meta f.item_meta) then None else
    ExtractName.NameMatcherMap.find_opt name_ctx f.item_meta.name
      (ExtractBuiltin.builtin_funs_map ()) in
  let type_info (d : type_decl) =
    if not (modeled_meta d.item_meta) then None else
    ExtractName.NameMatcherMap.find_opt name_ctx d.item_meta.name
      (ExtractBuiltin.builtin_types_map ()) in
  let impl_info (d : trait_impl) =
    if not (modeled_meta d.item_meta) then None else
    Option.bind (TraitDeclId.Map.find_opt d.impl_trait.id crate.trait_decls)
      (fun (t : trait_decl) ->
        ExtractName.NameMatcherMap.find_with_generics_opt name_ctx
          t.item_meta.name d.impl_trait.generics
          (ExtractBuiltin.builtin_trait_impls_map ())) in
  let live = ref AnyDeclIdSet.empty in
  let pending = ref [] in
  let add id = if not (AnyDeclIdSet.mem id !live) then (
    live := AnyDeclIdSet.add id !live; pending := id :: !pending) in
  let visitor = object (self)
    inherit [_] iter_crate as super
    method! visit_item_meta _ _ = ()
    method! visit_fun_source _ _ = ()
    method! visit_type_source _ _ = ()
    method! visit_global_source _ _ = ()
    method! visit_trait_impl_source _ _ = ()
    method! visit_trait_decl_source _ _ = ()
    method! visit_type_decl_id _ id = add (IdType id)
    method! visit_fun_decl_id _ id = add (IdFun id)
    method! visit_global_decl_id _ id = add (IdGlobal id)
    method! visit_trait_decl_id _ id = add (IdTraitDecl id)
    method! visit_trait_impl_id _ id = add (IdTraitImpl id)
    method! visit_type_decl_ref env (r : type_decl_ref) =
      let info = if not builtin_pruning then None else
        Option.bind (TypeDeclId.Map.find_opt r.id crate.type_decls)
          (fun d -> Option.map (fun info -> (d, info)) (type_info d)) in
      match info with
      | None -> super#visit_type_decl_ref env r
      | Some (d, info) ->
          self#visit_type_decl_id env r.id;
          self#visit_generic_args env
            (filtered_args d.item_meta.span info.keep_params None r.generics)
    method! visit_trait_impl_ref env (r : trait_impl_ref) =
      let info = if not builtin_pruning then None else
        Option.bind (TraitImplId.Map.find_opt r.id crate.trait_impls)
          (fun d -> Option.map (fun info -> (d, info)) (impl_info d)) in
      match info with
      | None -> super#visit_trait_impl_ref env r
      | Some (d, info) ->
          self#visit_trait_impl_id env r.id;
          self#visit_generic_args env
            (filtered_args d.item_meta.span info.keep_params info.keep_trait_clauses r.generics)
    method! visit_trait_ref env tr =
      match AppliedBuiltins.classify_reverse_trait crate tr with
      | Some (_,a,b) -> self#visit_ty env a; self#visit_ty env b;
          self#visit_trait_decl_ref env tr.trait_decl_ref.binder_value
      | None ->
      match AppliedZipDispatch.classify_trait crate tr with
      | Some (_,a,b) -> self#visit_ty env a; self#visit_ty env b;
          self#visit_trait_decl_ref env tr.trait_decl_ref.binder_value
      | None -> super#visit_trait_ref env tr
    method! visit_fn_ptr env fn =
      match fn.kind with
      | Fun id -> (match AppliedZipDispatch.classify_function crate id fn.generics with
          | Some (_, args) -> self#visit_generic_args env args
          | None ->
              let info = if not builtin_pruning then None else
                Option.bind (FunDeclId.Map.find_opt id crate.fun_decls)
                  (fun f -> Option.map (fun info -> (f, info)) (function_info f)) in
              (match info with
              | None -> super#visit_fn_ptr env fn
              | Some (f, info) ->
                  self#visit_fun_decl_id env id;
                  self#visit_generic_args env
                    (filtered_args f.item_meta.span info.keep_params info.keep_trait_clauses fn.generics)))
      | _ -> super#visit_fn_ptr env fn
    method! visit_fun_decl_ref env (r : fun_decl_ref) =
      let info = if not builtin_pruning then None else
        Option.bind (FunDeclId.Map.find_opt r.id crate.fun_decls)
          (fun f -> Option.map (fun info -> (f, info)) (function_info f)) in
      match info with
      | None -> super#visit_fun_decl_ref env r
      | Some (f, info) ->
          self#visit_fun_decl_id env r.id;
          self#visit_generic_args env
            (filtered_args f.item_meta.span info.keep_params info.keep_trait_clauses r.generics)
  end in
  (* With explicit Charon root selection, transitive local items (e.g. a derived
     Hash implementation used solely by an erased map dictionary) are not roots.
     Without explicit selection retain the previous conservative root policy. *)
  let selected_roots = builtin_pruning &&
    (crate.options.start_from <> [] || crate.options.start_from_if_exists <> []
     || crate.options.start_from_attribute <> [] || crate.options.start_from_pub) in
  AnyDeclIdSet.iter (fun id ->
    if selected_roots then (
      match crate_get_item_meta crate id with
      | Some m when m.started_from -> add id
      | _ -> ())
    else match id with
    | IdFun _ | IdTraitImpl _ ->
        (match crate_get_item_meta crate id with
         | Some m when m.is_local || m.started_from -> add id | _ -> ())
    | _ -> add id) eligible;
  while !pending <> [] do
    let id = match !pending with
      | id :: rest -> pending := rest; id
      | [] -> [%craise_opt_span] None "Missing pending dependency" in
    (* Retain complete recursive groups rather than splitting their semantics. *)
    List.iter (fun g -> let ids = Charon.GAstUtils.declaration_group_to_list g in
      if List.mem id ids then List.iter add ids) groups;
    match id with
    | IdFun id -> Option.iter (fun (f : fun_decl) ->
        let info = function_info f in
        let params = match info with
          | Some info when builtin_pruning ->
              filtered_params f.item_meta.span info.keep_params info.keep_trait_clauses f.generics
          | _ -> f.generics in
        visitor#visit_generic_params () params;
        visitor#visit_fun_sig () f.signature;
        if Option.is_none info then visitor#visit_fun_decl () f)
        (FunDeclId.Map.find_opt id crate.fun_decls)
    | IdTraitImpl id -> Option.iter (fun (d : trait_impl) ->
        match impl_info d with
        | Some info when builtin_pruning ->
            visitor#visit_generic_params ()
              (filtered_params d.item_meta.span info.keep_params info.keep_trait_clauses d.generics);
            visitor#visit_trait_decl_ref () d.impl_trait;
            List.iter (visitor#visit_trait_ref ()) d.implied_trait_refs;
            (* Pure simplification can turn a live dictionary projection into
               a direct method call (e.g. reference equality to slice equality).
               Keep real method declarations for the modeled record's supported
               fields. Erased dictionaries never reach this branch. *)
            let trait_info = Option.bind
              (TraitDeclId.Map.find_opt d.impl_trait.id crate.trait_decls)
              (fun (t : trait_decl) -> ExtractName.NameMatcherMap.find_opt
                name_ctx t.item_meta.name (ExtractBuiltin.builtin_trait_decls_map ())) in
            TraitMethodId.Map.iter (fun method_id (m : fun_decl_ref binder) ->
              let keep = match trait_info with
                | None -> true
                | Some info ->
                    let name = Charon.GAstUtils.get_method_name crate d.impl_trait.id method_id in
                    List.exists (fun (supported, _) -> supported = name) info.methods in
              if keep then (
                visitor#visit_generic_params () m.binder_params;
                visitor#visit_fun_decl_ref () m.binder_value)) d.methods
        | _ -> visitor#visit_trait_impl () d)
        (TraitImplId.Map.find_opt id crate.trait_impls)
    | IdType id -> Option.iter (fun (d : type_decl) ->
        match type_info d with
        | Some info when builtin_pruning ->
            visitor#visit_generic_params ()
              (filtered_params d.item_meta.span info.keep_params None d.generics)
        | _ -> visitor#visit_type_decl () d)
        (TypeDeclId.Map.find_opt id crate.type_decls)
    | IdGlobal id -> Option.iter (visitor#visit_global_decl ()) (GlobalDeclId.Map.find_opt id crate.global_decls)
    | IdTraitDecl id -> Option.iter (fun (d : trait_decl) ->
        let modeled = modeled_meta d.item_meta &&
          ExtractName.NameMatcherMap.mem name_ctx
            d.item_meta.name (ExtractBuiltin.builtin_trait_decls_map ()) in
        if modeled then visitor#visit_generic_params () d.generics
        else visitor#visit_trait_decl () d) (TraitDeclId.Map.find_opt id crate.trait_decls)
  done;
  let declarations = Some (List.filter (fun g ->
    List.exists (fun id -> AnyDeclIdSet.mem id !live)
      (Charon.GAstUtils.declaration_group_to_list g)) groups) in
  {crate with declarations})

(** Analysis still consumes the original call signatures, including arguments
    erased only when emitting a builtin application. Collect their real source
    type dependencies separately; do not invent borrow information or re-add
    these types to the emitted declarations. *)
let analysis_type_declarations (crate : crate)
    (emitted : type_declaration_group list) : type_declaration_group list =
  if not (builtin_pruning_enabled ()) then emitted else
  let needed = ref TypeDeclId.Set.empty in
  let pending = ref [] in
  let add id = if not (TypeDeclId.Set.mem id !needed) then (
    needed := TypeDeclId.Set.add id !needed; pending := id :: !pending) in
  let visitor add = object
    inherit [_] iter_crate
    method! visit_item_meta _ _ = ()
    method! visit_fun_source _ _ = ()
    method! visit_type_source _ _ = ()
    method! visit_global_source _ _ = ()
    method! visit_trait_impl_source _ _ = ()
    method! visit_trait_decl_source _ _ = ()
    method! visit_type_decl_id _ id = add id
  end in
  let roots = visitor add in
  List.iter (fun group -> List.iter (function
    | IdType id -> add id
    | IdFun id -> Option.iter (roots#visit_fun_decl ())
        (FunDeclId.Map.find_opt id crate.fun_decls)
    | IdGlobal id -> Option.iter (roots#visit_global_decl ())
        (GlobalDeclId.Map.find_opt id crate.global_decls)
    | IdTraitDecl id -> Option.iter (roots#visit_trait_decl ())
        (TraitDeclId.Map.find_opt id crate.trait_decls)
    | IdTraitImpl id -> Option.iter (roots#visit_trait_impl ())
        (TraitImplId.Map.find_opt id crate.trait_impls))
    (Charon.GAstUtils.declaration_group_to_list group))
    ([%silent_unwrap_opt_span] None crate.declarations);
  let graph = ref TypeDeclId.Map.empty in
  while !pending <> [] do
    let id = match !pending with
      | id :: rest -> pending := rest; id
      | [] -> [%craise_opt_span] None "Missing pending source type" in
    let d = [%unwrap_opt_span] None
      (TypeDeclId.Map.find_opt id crate.type_decls)
      "Missing source type declaration for builtin dependency analysis" in
    let deps = ref TypeDeclId.Set.empty in
    let fields = visitor (fun id ->
      deps := TypeDeclId.Set.add id !deps; add id) in
    (* Do not visit def_id itself: a nonrecursive type must not acquire a
       spurious self edge merely because its record stores its own identifier. *)
    fields#visit_generic_params () d.generics;
    fields#visit_type_decl_kind () d.kind;
    graph := TypeDeclId.Map.add id !deps !graph
  done;
  let module Scc = SCC.Make (TypeDeclId.Ord) in
  let graph_list = List.map (fun (id, deps) ->
    (id, Scc.S.of_list (TypeDeclId.Set.elements deps)))
    (TypeDeclId.Map.bindings !graph) in
  let sccs = Scc.compute graph_list in
  List.map (fun (_, ids) -> match ids with
    | [id] ->
        let deps = [%silent_unwrap_opt_span] None (TypeDeclId.Map.find_opt id !graph) in
        if TypeDeclId.Set.mem id deps then RecGroup ids else NonRecGroup id
    | [] -> [%craise_opt_span] None "Empty source type dependency group"
    | _ -> RecGroup ids)
    (SCC.SccId.Map.bindings sccs.sccs)

(** Source signatures of replaced direct uses remain available to the symbolic
    interpreter/type translator. Only bodies/emission are pruned. This set is
    recomputed from live declarations, and never marks a generic use builtin. *)
let signature_dependencies (crate : crate) =
  let selected = ref FunDeclId.Map.empty in
  if AppliedZipDispatch.enabled () then (
    let visitor = object
      inherit [_] iter_crate as super
      method! visit_fn_ptr env fn =
        (match fn.kind with
        | Fun id when Option.is_some (AppliedZipDispatch.classify_function crate id fn.generics) ->
            Option.iter (fun f -> selected := FunDeclId.Map.add id f !selected)
              (FunDeclId.Map.find_opt id crate.fun_decls)
        | _ -> ());
        super#visit_fn_ptr env fn
    end in
    List.iter (fun group -> List.iter (function
      | IdFun id -> Option.iter (visitor#visit_fun_decl ()) (FunDeclId.Map.find_opt id crate.fun_decls)
      | IdTraitImpl id -> Option.iter (visitor#visit_trait_impl ()) (TraitImplId.Map.find_opt id crate.trait_impls)
      | IdGlobal id -> Option.iter (visitor#visit_global_decl ()) (GlobalDeclId.Map.find_opt id crate.global_decls)
      | IdType id -> Option.iter (visitor#visit_type_decl ()) (TypeDeclId.Map.find_opt id crate.type_decls)
      | IdTraitDecl id -> Option.iter (visitor#visit_trait_decl ()) (TraitDeclId.Map.find_opt id crate.trait_decls))
      (Charon.GAstUtils.declaration_group_to_list group))
      ([%silent_unwrap_opt_span] None crate.declarations));
  !selected
