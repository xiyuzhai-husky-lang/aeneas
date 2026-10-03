module
public import Aeneas.Std.HashSet
public section
open Aeneas.Std Result
namespace Aeneas.Std

@[expose, rust_fun "core::borrow::{core::borrow::Borrow<&'0 @T, @T>}::borrow"]
def core.borrow.Borrow.Shared.borrow {T : Type} (value : T) : Result T := ok value

@[expose, reducible, rust_trait_impl "core::borrow::Borrow<&'0 @T, @T>"]
def core.borrow.Borrow.Shared (T : Type) : core.borrow.Borrow T T :=
  ⟨core.borrow.Borrow.Shared.borrow⟩

@[expose, rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type} (value : T) : Result T := ok value

namespace std.collections.hash.set.HashSet
open std.collections.hash.map
variable {T S A Q : Type}

/-- The same lawful, pure, hash-compatible borrowed-key contents boundary as
`HashMap::get`. The actual Borrow/Eq calls, including failure/divergence, are
retained. Hash-table layout and hashing remain the standard library boundary. -/
@[expose, rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::contains"
  (keepParams := [true, true, true, true, false])
  (keepTraitClauses := [false, false, false, true, false, true])]
def containsContents (borrow : core.borrow.Borrow T Q) (eq : core.cmp.Eq Q)
    (self : HashSet T S A) (query : Q) : Result Bool := do
  let found ← HashMap.getContents borrow eq self query
  ok found.isSome

theorem containsContents_exact [DecidableEq Q]
    (borrow : core.borrow.Borrow T Q) (eq : core.cmp.Eq Q) (keyView : T → Q)
    (borrowLaw : HashMap.ExactBorrow borrow.borrow keyView)
    (eqLaw : HashMap.ExactEq eq.partialEqInst.eq)
    (self : HashSet T S A) (query : Q) :
    containsContents borrow eq self query = ok
      (HashMap.lookupEntries (self.entries.map fun entry => (keyView entry.1, entry.2)) query).isSome := by
  simp [containsContents, HashMap.getContents_exact borrow eq keyView borrowLaw eqLaw]

theorem containsContents_found (borrow : core.borrow.Borrow T Q) (eq : core.cmp.Eq Q)
    (self : HashSet T S A) (query : Q)
    (found : HashMap.getContents borrow eq self query = ok (some ())) :
    containsContents borrow eq self query = ok true := by
  simp [containsContents, found]

theorem containsContents_missing (borrow : core.borrow.Borrow T Q) (eq : core.cmp.Eq Q)
    (self : HashSet T S A) (query : Q)
    (found : HashMap.getContents borrow eq self query = ok none) :
    containsContents borrow eq self query = ok false := by
  simp [containsContents, found]

end std.collections.hash.set.HashSet
end Aeneas.Std
