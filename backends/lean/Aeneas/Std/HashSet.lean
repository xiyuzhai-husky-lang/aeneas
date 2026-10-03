module
public import Aeneas.Std.HashMap
import all Aeneas.Std.HashMap
public section
open Aeneas.Std Result
namespace Aeneas.Std.std.collections.hash.set

/-! Standard HashSet finite-contents abstraction. A set is the existing HashMap
contents witness with unit values, exactly matching the standard library's
map-backed set interface. This shares HashMap's lawful, total, pure Hash/Eq
boundary and does not model buckets, iteration order, allocator failures, or
hashbrown's unsafe internals. Insertion retains an already-present element.
Equality failures/divergence are preserved by the existing Result traversal. -/

@[rust_type "std::collections::hash::set::HashSet"]
abbrev HashSet (T S A : Type) := hash.map.HashMap T Unit S A

namespace HashSet
open hash.map
variable {T S A : Type}

@[expose, rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::insert"
  (keepParams := [true, true, true, false])
  (keepTraitClauses := [true, false, false])]
def insertContents (eq : core.cmp.Eq T) (self : HashSet T S A) (value : T) :
    Result (Bool × HashSet T S A) := do
  let (previous, updated) ← HashMap.insertContents eq self value ()
  match previous with
  | some _ => ok (false, self)
  | none => ok (true, updated)

def contains [DecidableEq T] (self : HashSet T S A) (value : T) : Prop :=
  value ∈ self.entries.map Prod.fst

instance [DecidableEq T] (self : HashSet T S A) (value : T) :
    Decidable (contains self value) := inferInstanceAs (Decidable (value ∈ self.entries.map Prod.fst))

private theorem put_unit_existing [DecidableEq T] (entries : List (T × Unit))
    (value : T) (present : value ∈ entries.map Prod.fst) :
    HashMap.putEntries entries value () = entries := by
  induction entries with
  | nil => simp at present
  | cons entry rest ih =>
    rcases entry with ⟨stored, ⟨⟩⟩
    by_cases same : value = stored
    · simp [HashMap.putEntries, same]
    · simp only [List.map_cons, List.mem_cons] at present
      have tail : value ∈ rest.map Prod.fst := present.resolve_left same
      simp [HashMap.putEntries, same, ih tail]

/-- Even without exact-equality laws, a reported existing entry returns the
original table witness, retaining its original representative. -/
theorem insertContents_duplicate_result (eq : core.cmp.Eq T)
    (self candidate : HashSet T S A) (value : T) (previous : Unit)
    (found : HashMap.insertContents eq self value () = ok (some previous, candidate)) :
    insertContents eq self value = ok (false, self) := by
  simp [insertContents, found]

theorem insertContents_exact [DecidableEq T] (eq : core.cmp.Eq T)
    (eqLaw : HashMap.ExactEq eq.partialEqInst.eq) (self : HashSet T S A) (value : T) :
    insertContents eq self value =
      ok (decide (¬ contains self value), ⟨HashMap.putEntries self.entries value ()⟩) := by
  simp only [insertContents, HashMap.insertContents_exact _ eqLaw, bind_tc_ok]
  cases found : self.view value with
  | none =>
    have absent : ¬ contains self value :=
      (HashMap.lookupEntries_none_iff self.entries value).mp found
    simp [absent]
  | some previous =>
    have present : contains self value := by
      by_contra absent
      have missing := (HashMap.lookupEntries_none_iff self.entries value).mpr absent
      simp only [HashMap.view] at found
      rw [found] at missing
      contradiction
    simp [present, put_unit_existing self.entries value present]

theorem insertContents_present [DecidableEq T] (eq : core.cmp.Eq T)
    (eqLaw : HashMap.ExactEq eq.partialEqInst.eq) (self : HashSet T S A) (value : T)
    (present : contains self value) :
    insertContents eq self value = ok (false, self) := by
  rw [insertContents_exact eq eqLaw]
  simp only [present, not_true_eq_false, decide_false]
  rw [put_unit_existing self.entries value present]

theorem insertContents_spec [DecidableEq T] (eq : core.cmp.Eq T)
    (eqLaw : HashMap.ExactEq eq.partialEqInst.eq) (self : HashSet T S A) (value : T)
    (wellFormed : self.WellFormed) :
    ∃ inserted updated, insertContents eq self value = ok (inserted, updated) ∧
      (inserted = true ↔ ¬ contains self value) ∧ updated.WellFormed ∧
      (∀ query, contains updated query ↔ query = value ∨ contains self query) ∧
      (inserted = false → updated = self) := by
  refine ⟨decide (¬ contains self value), ⟨HashMap.putEntries self.entries value ()⟩,
    insertContents_exact eq eqLaw self value, by simp, ?_, ?_, ?_⟩
  · exact HashMap.putEntries_nodup self.entries value () wellFormed
  · intro query
    simp only [contains, HashMap.putEntries_keys]
    split
    · rename_i present
      constructor
      · exact Or.inr
      · rintro (rfl | found)
        · exact present
        · exact found
    · simp only [List.mem_append, List.mem_singleton]
      exact or_comm
  · intro duplicate
    have present : contains self value := by simpa using duplicate
    exact congrArg HashMap.mk (put_unit_existing self.entries value present)

/-- Standard empty constructor with the same hidden RandomState default as
`HashMap::new`; native contents are empty before any insertion. -/
@[expose, rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, std::hash::random::RandomState, alloc::alloc::Global>}::new"]
def new (T : Type) : Result (HashSet T std.hash.random.RandomState Global) :=
  HashMap.new T Unit

@[simp] theorem new_empty (T : Type) : new T = ok ⟨[]⟩ := by
  simp [new]

theorem new_spec (T : Type) [DecidableEq T] :
    ∃ empty, new T = ok empty ∧ empty.WellFormed ∧ ∀ value, ¬ contains empty value := by
  refine ⟨⟨[]⟩, new_empty T, ?_, ?_⟩
  · simp [HashMap.WellFormed]
  · intro value
    simp [contains]

#print axioms new_empty
#print axioms new_spec
#print axioms insertContents_exact
#print axioms insertContents_present
#print axioms insertContents_spec
end HashSet
end Aeneas.Std.std.collections.hash.set
