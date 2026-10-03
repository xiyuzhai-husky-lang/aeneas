open Aeneas
open Types
open LlbcAst
open LlbcAstUtils

let require b msg = if not b then failwith msg
let require_none value msg = require (Option.is_none value) msg

let () =
  Config.progress_bar := false;
  Config.opt_backend := Some Config.Lean;
  Config.applied_slice_zip := true;
  Config.filter_trait_impl_methods := true;
  let original = match LlbcOfJson.crate_of_json_file Sys.argv.(1) with
    | Ok c -> c | Error s -> failwith s in
  let crate = PrePasses.apply_passes original in
  let traits = ref [] and functions = ref [] in
  let parents = ref [] in
  let visitor = object
    inherit [_] iter_crate as super
    method! visit_trait_ref env tr =
      (match AppliedBuiltins.classify_trait crate tr with
      | Some _ -> traits := tr :: !traits | None -> ());
      (match tr.kind with
      | TraitImpl r -> (match AppliedBuiltins.instantiate_impl crate r with
          | Some (d, subst, expected) when expected = tr.trait_decl_ref.binder_value ->
              List.iteri (fun i original ->
                let resolved = Charon.Substitute.trait_ref_substitute subst original in
                match AppliedBuiltins.classify_trait crate resolved with
                | Some expected -> parents := (tr, i, resolved, expected) :: !parents
                | None -> ()) d.implied_trait_refs
          | _ -> ())
      | _ -> ());
      super#visit_trait_ref env tr
    method! visit_fn_ptr env fn =
      (match fn.kind with
      | Fun id when Option.is_some (AppliedBuiltins.classify_function crate id fn.generics) ->
          functions := (id, fn.generics) :: !functions
      | _ -> ()); super#visit_fn_ptr env fn
  end in
  visitor#visit_crate () crate;
  require (!traits <> [] || !functions <> []) "No real applied reference found";
  let checks = ref 0 in
  List.iter (fun (id,args) ->
    let check args label = incr checks;
      require_none (AppliedBuiltins.classify_function crate id args) label in
    check {args with types = []} "Accepted missing types";
    check {args with trait_refs = []} "Accepted missing witnesses";
    check {args with trait_refs = args.trait_refs @ args.trait_refs} "Accepted doubled witnesses";
    let f = FunDeclId.Map.find id crate.fun_decls in
    let local = {crate with fun_decls = FunDeclId.Map.add id
      {f with item_meta = {f.item_meta with is_local = true}} crate.fun_decls} in
    incr checks;
    require_none (AppliedBuiltins.classify_function local id args) "Accepted local lookalike";
    (* Root preservation is an in-memory policy unit, never extraction evidence. *)
    let rooted = {crate with fun_decls = FunDeclId.Map.add id
      {f with item_meta = {f.item_meta with started_from = true}} crate.fun_decls;
      declarations = Some (FunGroup (NonRecGroup id) :: Option.get crate.declarations)} in
    let rooted = AppliedBuiltinUses.prune rooted in
    incr checks;
    require (List.exists (fun g -> List.mem (IdFun id)
      (Charon.GAstUtils.declaration_group_to_list g)) (Option.get rooted.declarations))
      "Pruned explicitly rooted generic method") !functions;
  List.iter (fun (tr : trait_ref) ->
    incr checks; require_none (AppliedBuiltins.classify_trait crate {tr with kind = Self})
      "Accepted unresolved witness";
    match tr.kind with
    | TraitImpl r ->
        let check r label = incr checks;
          require_none (AppliedBuiltins.classify_trait crate {tr with kind = TraitImpl r}) label in
        check {r with generics = {r.generics with types=[]}} "Accepted missing impl args";
        check {r with generics = {r.generics with trait_refs=[]}} "Accepted missing slice witness";
        let bad = List.map (fun (x : trait_ref) -> {x with kind = Self}) r.generics.trait_refs in
        check {r with generics = {r.generics with trait_refs=bad}} "Accepted unresolved slice witness"
    | _ -> ()) !traits;
  List.iter (fun (parent, i, (resolved : trait_ref), expected) ->
    let projected = {resolved with kind = ParentClause (parent, TraitClauseId.of_int i)} in
    incr checks;
    require (AppliedBuiltins.classify_trait crate projected = Some expected)
      "Original applied parent resolution did not select the same dictionary";
    incr checks;
    require_none (AppliedBuiltins.classify_trait crate
      {projected with trait_decl_ref = parent.trait_decl_ref})
      "Accepted incorrect advertised parent type") !parents;
  if Array.length Sys.argv > 2 then require (!parents <> []) "No concrete parent control found";
  Printf.printf "Applied classifier negative/preservation checks: %d; real function uses: %d; real trait uses: %d; concrete parent controls: %d\n"
    !checks (List.length !functions) (List.length !traits) (List.length !parents)
