import Aeneas.Std.SliceZip
import Lean.Util.CollectAxioms

run_elab do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let expected := #[``SliceZipPrototype.window_length, ``SliceZipPrototype.window_pair_at,
    ``SliceZipPrototype.foldWindow_nil, ``SliceZipPrototype.foldWindow_cons,
    ``SliceZipPrototype.foldWindow_callback_fail, ``SliceZipPrototype.foldWindow_callback_div,
    ``SliceZipPrototype.foldWindow_callback_state, ``SliceZipPrototype.defaultFold_of_produces,
    ``SliceZipPrototype.sliceZip_produces, ``SliceZipPrototype.fold_eq_modeled_next]
  for name in expected do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing theorem {name}"
  let mut decls := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "SliceZipPrototype." ||
       name.toString.startsWith "Aeneas.Std.core.iter.adapters.zip.SliceZip." ||
       name.toString.startsWith "Aeneas.Std.core.iter.traits.iterator.IteratorSliceZip" then
      if let .axiomInfo _ := info then throwError "Unexpected axiom {name}"
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected transitive axiom {axiomName} in {name}"
      decls := decls + 1
      if let .thmInfo _ := info then theorems := theorems + 1
  Lean.logInfo m!"SliceZip logical/library audit: {expected.size} public theorems, {theorems} total theorem declarations, {decls} scoped declarations. No native unsafe specialization correspondence claimed."
