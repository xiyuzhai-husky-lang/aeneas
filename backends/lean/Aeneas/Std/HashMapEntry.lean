module
public import Aeneas.Std.HashMap
import all Aeneas.Std.HashMap
public section
open Aeneas.Std Result
namespace Aeneas.Std.std.collections.hash.map

/-- Standard `Entry` mutable contents lens. The original lookup determines the
occupied/vacant case and captures the exact update position. The backward value
is consumed by `HashMap.entry`'s map writeback; it never repeats Hash/Eq callbacks.
This has the same lawful pure Hash/Eq and allocation/destruction boundary as
HashMap. Native bucket pointers and the hidden allocator are abstracted. -/
@[rust_type "std::collections::hash::map::Entry" (mutRegions := #[0]) (body := .opaque)]
structure Entry (K V A : Type) where
  contents : List (K × V)
  value : Option V
  write : V → List (K × V)

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::entry"
  (keepParams := [true, true, true, true, false])
  (keepTraitClauses := [true, false, false])]
def HashMap.entryContents {K V S A : Type} (eq : core.cmp.Eq K)
    (self : HashMap K V S A) (key : K) :
    Result (Entry K V A × (Entry K V A → HashMap K V S A)) := do
  let (found, back) ← HashMap.getMutWith (fun stored => ok stored) eq.partialEqInst.eq self.entries key
  let write := match found with
    | some _ => fun updated => back (some updated)
    | none => fun updated => self.entries ++ [(key,updated)]
  ok (⟨self.entries,found,write⟩,fun updated => ⟨updated.contents⟩)

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::Entry<'a, @K, @V, alloc::alloc::Global>}::or_default"]
def Entry.or_default {K V : Type} (defaultV : core.default.Default V)
    (self : Entry K V Global) : Result (V × (V → Entry K V Global)) := do
  let value ← match self.value with
    | some value => ok value
    | none => defaultV.default
  ok (value,fun updated => {self with contents := self.write updated, value := some updated})

theorem Entry.or_default_occupied {K V : Type} (defaultV : core.default.Default V)
    (self : Entry K V Global) (value : V) (occupied : self.value = some value) :
    or_default defaultV self =
      ok (value,fun updated => {self with contents := self.write updated,value := some updated}) := by
  simp [or_default,occupied]

theorem Entry.or_default_vacant {K V : Type} (defaultV : core.default.Default V)
    (self : Entry K V Global) (vacant : self.value = none) :
    or_default defaultV self = (do
      let value ← defaultV.default
      ok (value,fun updated => {self with contents := self.write updated,value := some updated})) := by
  simp [or_default,vacant]

theorem Entry.or_default_vacant_fail {K V : Type} (defaultV : core.default.Default V)
    (self : Entry K V Global) (vacant : self.value = none) (error : Error)
    (failed : defaultV.default = fail error) : or_default defaultV self = fail error := by
  simp [or_default,vacant,failed]

theorem Entry.or_default_vacant_div {K V : Type} (defaultV : core.default.Default V)
    (self : Entry K V Global) (vacant : self.value = none)
    (diverged : defaultV.default = div) : or_default defaultV self = div := by
  simp [or_default,vacant,diverged]

private theorem putEntries_absent [DecidableEq K] (entries : List (K × V)) (key : K)
    (absent : HashMap.lookupEntries entries key = none) (value : V) :
    HashMap.putEntries entries key value = entries ++ [(key,value)] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨stored,old⟩
    by_cases hit : key = stored
    · simp [HashMap.lookupEntries,hit] at absent
    · simp only [HashMap.lookupEntries,if_neg hit] at absent
      simp [HashMap.putEntries,hit,ih absent]

/-- Exact composition of the two real library calls and their mutable
writebacks. An occupied key retains its original representative and all other
entries; a vacant key is inserted once after the default callback succeeds. -/
theorem HashMap.entry_or_default_exact {K V S : Type} [DecidableEq K]
    (eq : core.cmp.Eq K) (law : HashMap.ExactEq eq.partialEqInst.eq)
    (defaultV : core.default.Default V) (self : HashMap K V S Global) (key : K) :
    (do let (entry,mapBack) ← entryContents eq self key
        let (value,entryBack) ← Entry.or_default defaultV entry
        ok (value,fun updated => mapBack (entryBack updated))) =
      (do let value ← match self.view key with
            | some value => ok value
            | none => defaultV.default
          ok (value,fun updated => (⟨HashMap.putEntries self.entries key updated⟩ : HashMap K V S Global))) := by
  have looked : HashMap.getMutWith (fun stored : K => ok stored) eq.partialEqInst.eq self.entries key =
      ok (self.view key,HashMap.replaceEntries id self.entries key) := by
    simpa [HashMap.view] using HashMap.getMutWith_exact (fun stored : K => ok stored) id eq.partialEqInst.eq
      (by intro; rfl) law self.entries key
  simp only [entryContents,looked,bind_tc_ok,Entry.or_default]
  cases found : self.view key with
  | some old =>
    simp only [HashMap.view] at found
    simp only [bind_tc_ok]
    congr 2
    funext updated
    exact congrArg HashMap.mk (HashMap.replaceEntries_present self.entries key old updated found)
  | none =>
    simp only [HashMap.view] at found
    simp only [bind_assoc_eq,bind_tc_ok]
    congr 1
    funext value
    congr 2
    funext updated
    exact congrArg HashMap.mk (putEntries_absent self.entries key found updated).symm

/-- No exact-key equality assumption is needed to retain the representative
stored in an occupied slot, even when the key's lawful Eq quotient is coarser. -/
theorem HashMap.entry_or_default_first_hit {K V S : Type}
    (eq : core.cmp.Eq K) (defaultV : core.default.Default V)
    (key stored : K) (old : V) (rest : List (K × V))
    (hit : eq.partialEqInst.eq key stored = ok true) :
    (do let (entry,mapBack) ← entryContents eq (⟨(stored,old)::rest⟩ : HashMap K V S Global) key
        let (value,entryBack) ← Entry.or_default defaultV entry
        ok (value,fun updated => mapBack (entryBack updated))) =
      ok (old,fun updated => (⟨(stored,updated)::rest⟩ : HashMap K V S Global)) := by
  simp [entryContents,getMutWith,hit,Entry.or_default]

/-- The exact forward/update/backward pipeline used by a native mutable
entry client. The update callback is called once after lookup/default succeeds. -/
theorem HashMap.entry_or_default_modify {K V S : Type} [DecidableEq K]
    (eq : core.cmp.Eq K) (law : HashMap.ExactEq eq.partialEqInst.eq)
    (defaultV : core.default.Default V) (self : HashMap K V S Global) (key : K)
    (update : V → Result V) :
    (do let (entry,mapBack) ← HashMap.entryContents eq self key
        let (value,entryBack) ← Entry.or_default defaultV entry
        let updated ← update value
        ok (mapBack (entryBack updated))) =
      (do let value ← match self.view key with
            | some value => ok value
            | none => defaultV.default
          let updated ← update value
          ok (⟨HashMap.putEntries self.entries key updated⟩ : HashMap K V S Global)) := by
  have h := congrArg (fun r : Result (V × (V → HashMap K V S Global)) => do
    let (value,back) ← r
    let updated ← update value
    ok (back updated)) (HashMap.entry_or_default_exact eq law defaultV self key)
  cases found : self.view key <;> simpa only [found,bind_assoc_eq,bind_tc_ok,uncurry] using h

#print axioms HashMap.entry_or_default_first_hit
#print axioms Entry.or_default_occupied
#print axioms Entry.or_default_vacant_fail
#print axioms Entry.or_default_vacant_div
#print axioms HashMap.entry_or_default_exact
end Aeneas.Std.std.collections.hash.map
