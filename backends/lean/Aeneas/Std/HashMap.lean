module
public import Aeneas.Std.Core.Hash
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Alloc
public import Aeneas.Std.Vec
public section

/-!
Logical contents model of Rust's standard `HashMap`, at the same external-library
boundary as the Vec/Slice models. The list witnesses finite contents; it does not
replace the Rust implementation, which still uses its normal hash table.

The correspondence to the native library is restricted to lawful, total, pure
Hash/Eq/Borrow implementations with stable keys and hash-compatible borrowed keys.
Hashing, random seeds, bucket/probe order and allocator/resource behavior are
abstracted. The filtered wrappers erase unobserved hash dictionaries only
under this boundary. In particular, this is not a verification of hashbrown's
unsafe internals, arbitrary effectful callbacks, or allocation success.

Borrow and equality remain Result callbacks, so their failures and divergence are
preserved by the witness traversal. The traversal order is not a claim about the
native table's callback order. Theorems connecting it to finite map contents
explicitly require exact equality and borrowing laws; those laws are not axioms.
-/
namespace Aeneas.Std

open Result

@[rust_trait "core::borrow::Borrow"]
structure core.borrow.Borrow (Self Borrowed : Type) where
  borrow : Self → Result Borrowed

@[expose, rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} (self : T) : Result T := ok self

@[expose, reducible, rust_trait_impl "core::borrow::Borrow<@T, @T>"]
def core.borrow.Borrow.Blanket (T : Type) : core.borrow.Borrow T T :=
  { borrow := core.borrow.Borrow.Blanket.borrow }

/-- The seed is unobservable through the contents-only interface modeled here. -/
@[rust_type "std::hash::random::RandomState"]
structure std.hash.random.RandomState where
  mk ::

@[expose, rust_fun "std::hash::random::{core::default::Default<std::hash::random::RandomState>}::default"]
def std.hash.random.RandomState.Insts.CoreDefaultDefault.default :
    Result std.hash.random.RandomState := ok ⟨⟩

@[expose, reducible, rust_trait_impl "core::default::Default<std::hash::random::RandomState>"]
def std.hash.random.RandomState.Insts.CoreDefaultDefault :
    core.default.Default std.hash.random.RandomState :=
  { default := std.hash.random.RandomState.Insts.CoreDefaultDefault.default }

namespace std.collections.hash.map

/-- Finite contents; S and A are phantom because seed/allocator are unobserved. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure HashMap (K V S A : Type) where
  entries : List (K × V)

namespace HashMap

variable {K V S A Q : Type}

/-- Exact semantic equality, required in proofs and not assumed by the dictionary. -/
def ExactEq [DecidableEq Q] (eq : Q → Q → Result Bool) : Prop :=
  ∀ query stored, eq query stored = ok (decide (query = stored))

def ExactBorrow (borrow : K → Result Q) (view : K → Q) : Prop :=
  ∀ key, borrow key = ok (view key)

def lookupEntries [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (stored, value) :: rest, query =>
      if query = stored then some value else lookupEntries rest query

/-- Replacing a value retains the original stored key. -/
def putEntries [DecidableEq K] : List (K × V) → K → V → List (K × V)
  | [], key, value => [(key, value)]
  | (stored, old) :: rest, key, value =>
      if key = stored then (stored, value) :: rest
      else (stored, old) :: putEntries rest key value

/-- Remove the first matching borrowed key, retaining every other stored key/value. -/
def eraseEntries [DecidableEq Q] (keyView : K → Q) :
    List (K × V) → Q → List (K × V)
  | [], _ => []
  | (stored, value) :: rest, query =>
      if query = keyView stored then rest
      else (stored, value) :: eraseEntries keyView rest query

@[expose]
def removeWith (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (Option V × List (K × V))
  | [], _ => ok (none, [])
  | (stored, value) :: rest, query => do
      let borrowed ← borrow stored
      let same ← eq query borrowed
      if same then ok (some value, rest)
      else
        let (previous, updated) ← removeWith borrow eq rest query
        ok (previous, (stored, value) :: updated)

@[expose]
def lookupWith (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (Option V)
  | [], _ => ok none
  | (stored, value) :: rest, query => do
      let borrowed ← borrow stored
      let same ← eq query borrowed
      if same then ok (some value) else lookupWith borrow eq rest query

@[expose]
def insertWith (eq : K → K → Result Bool) :
    List (K × V) → K → V → Result (Option V × List (K × V))
  | [], key, value => ok (none, [(key, value)])
  | (stored, old) :: rest, key, value => do
      let same ← eq key stored
      if same then ok (some old, (stored, value) :: rest)
      else
        let (previous, updated) ← insertWith eq rest key value
        ok (previous, (stored, old) :: updated)

@[expose, rust_fun
  "std::collections::hash::map::{core::default::Default<std::collections::hash::map::HashMap<@K, @V, @S, alloc::alloc::Global>>}::default"]
def defaultContents (K V : Type) {S : Type} (defaultS : core.default.Default S) :
    Result (HashMap K V S Global) := do
  let _ ← defaultS.default
  ok ⟨[]⟩

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"
  (keepParams := [true, true, true, true, true, false])
  (keepTraitClauses := [false, false, false, true, false, true])]
def getContents (borrow : core.borrow.Borrow K Q) (eq : core.cmp.Eq Q)
    (self : HashMap K V S A) (query : Q) : Result (Option V) :=
  lookupWith borrow.borrow eq.partialEqInst.eq self.entries query

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert"
  (keepParams := [true, true, true, true, false])
  (keepTraitClauses := [true, false, false])]
def insertContents (eq : core.cmp.Eq K) (self : HashMap K V S A) (key : K)
    (value : V) : Result (Option V × HashMap K V S A) := do
  let (previous, updated) ← insertWith eq.partialEqInst.eq self.entries key value
  ok (previous, ⟨updated⟩)

@[expose, rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::remove"
  (keepParams := [true, true, true, true, true, false])
  (keepTraitClauses := [false, false, false, true, false, true])]
def removeContents (borrow : core.borrow.Borrow K Q) (eq : core.cmp.Eq Q)
    (self : HashMap K V S A) (query : Q) : Result (Option V × HashMap K V S A) := do
  let (previous, updated) ← removeWith borrow.borrow eq.partialEqInst.eq self.entries query
  ok (previous, ⟨updated⟩)

@[expose]
def remove {H : Type} (_ : core.cmp.Eq K) (_ : core.hash.Hash K)
    (_ : core.hash.BuildHasher S H) (borrow : core.borrow.Borrow K Q)
    (_ : core.hash.Hash Q) (eq : core.cmp.Eq Q) (self : HashMap K V S A)
    (query : Q) : Result (Option V × HashMap K V S A) :=
  removeContents borrow eq self query

/-- Unfiltered signature matching the Rust method's trait arguments. -/
@[expose]
def get {H : Type} (_ : core.cmp.Eq K) (_ : core.hash.Hash K)
    (_ : core.hash.BuildHasher S H) (borrow : core.borrow.Borrow K Q)
    (_ : core.hash.Hash Q) (eq : core.cmp.Eq Q) (self : HashMap K V S A)
    (query : Q) : Result (Option V) := getContents borrow eq self query

@[expose]
def insert {H : Type} (eq : core.cmp.Eq K) (_ : core.hash.Hash K)
    (_ : core.hash.BuildHasher S H) (self : HashMap K V S A) (key : K)
    (value : V) : Result (Option V × HashMap K V S A) :=
  insertContents eq self key value

/-- A pure observation for client invariants; no Rust method is registered here. -/
def view [DecidableEq K] (self : HashMap K V S A) (key : K) : Option V :=
  lookupEntries self.entries key

def WellFormed (self : HashMap K V S A) : Prop :=
  (self.entries.map Prod.fst).Nodup

@[simp] theorem lookupEntries_none_iff [DecidableEq K]
    (entries : List (K × V)) (key : K) :
    lookupEntries entries key = none ↔ key ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookupEntries]
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      by_cases h : key = stored <;> simp [lookupEntries, h, ih]

@[simp] theorem lookupEntries_put_same [DecidableEq K]
    (entries : List (K × V)) (key : K) (value : V) :
    lookupEntries (putEntries entries key value) key = some value := by
  induction entries with
  | nil => simp [putEntries, lookupEntries]
  | cons entry rest ih =>
      rcases entry with ⟨stored, old⟩
      by_cases h : key = stored <;> simp [putEntries, lookupEntries, h, ih]

theorem lookupEntries_put_other [DecidableEq K]
    (entries : List (K × V)) (key query : K) (value : V) (h : query ≠ key) :
    lookupEntries (putEntries entries key value) query = lookupEntries entries query := by
  induction entries with
  | nil => simp [putEntries, lookupEntries, h]
  | cons entry rest ih =>
      rcases entry with ⟨stored, old⟩
      by_cases hk : key = stored
      · subst key
        simp [putEntries, lookupEntries, h]
      · by_cases hq : query = stored <;> simp [putEntries, lookupEntries, hk, hq, ih]

theorem putEntries_keys [DecidableEq K]
    (entries : List (K × V)) (key : K) (value : V) :
    (putEntries entries key value).map Prod.fst =
      if key ∈ entries.map Prod.fst then entries.map Prod.fst
      else entries.map Prod.fst ++ [key] := by
  induction entries with
  | nil => simp [putEntries]
  | cons entry rest ih =>
      rcases entry with ⟨stored, old⟩
      by_cases hk : key = stored
      · subst key
        simp [putEntries]
      · rw [putEntries, if_neg hk]
        change stored :: (putEntries rest key value).map Prod.fst =
          if key ∈ stored :: rest.map Prod.fst then stored :: rest.map Prod.fst
          else (stored :: rest.map Prod.fst) ++ [key]
        rw [ih]
        by_cases hr : key ∈ rest.map Prod.fst <;> simp [hr, hk]

theorem putEntries_nodup [DecidableEq K] (entries : List (K × V)) (key : K)
    (value : V) (unique : (entries.map Prod.fst).Nodup) :
    ((putEntries entries key value).map Prod.fst).Nodup := by
  rw [putEntries_keys]
  split
  · exact unique
  · rename_i absent
    simpa using List.Nodup.concat absent unique

theorem lookupWith_exact [DecidableEq Q]
    (borrow : K → Result Q) (keyView : K → Q) (eq : Q → Q → Result Bool)
    (borrowLaw : ExactBorrow borrow keyView) (eqLaw : ExactEq eq)
    (entries : List (K × V)) (query : Q) :
    lookupWith borrow eq entries query =
      ok (lookupEntries (entries.map fun entry => (keyView entry.1, entry.2)) query) := by
  unfold ExactBorrow at borrowLaw
  unfold ExactEq at eqLaw
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      simp only [lookupWith, borrowLaw, eqLaw, bind_tc_ok, decide_eq_true_eq,
        List.map_cons, lookupEntries]
      split <;> simp_all

theorem insertWith_exact [DecidableEq K] (eq : K → K → Result Bool)
    (eqLaw : ExactEq eq) (entries : List (K × V)) (key : K) (value : V) :
    insertWith eq entries key value =
      ok (lookupEntries entries key, putEntries entries key value) := by
  unfold ExactEq at eqLaw
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, old⟩
      simp only [insertWith, eqLaw, bind_tc_ok, decide_eq_true_eq,
        lookupEntries, putEntries]
      split <;> simp_all only [bind_tc_ok]

theorem getContents_exact [DecidableEq Q] (borrow : core.borrow.Borrow K Q)
    (eq : core.cmp.Eq Q) (keyView : K → Q)
    (borrowLaw : ExactBorrow borrow.borrow keyView) (eqLaw : ExactEq eq.partialEqInst.eq)
    (self : HashMap K V S A) (query : Q) :
    getContents borrow eq self query =
      ok (lookupEntries (self.entries.map fun entry => (keyView entry.1, entry.2)) query) :=
  lookupWith_exact borrow.borrow keyView eq.partialEqInst.eq borrowLaw eqLaw self.entries query

theorem getContents_identity [DecidableEq K] (eq : core.cmp.Eq K)
    (eqLaw : ExactEq eq.partialEqInst.eq) (self : HashMap K V S A) (key : K) :
    getContents (core.borrow.Borrow.Blanket K) eq self key = ok (self.view key) := by
  have h := getContents_exact (core.borrow.Borrow.Blanket K) eq id (by intro; rfl)
    eqLaw self key
  simpa [view] using h

theorem insertContents_exact [DecidableEq K] (eq : core.cmp.Eq K)
    (eqLaw : ExactEq eq.partialEqInst.eq) (self : HashMap K V S A) (key : K) (value : V) :
    insertContents eq self key value =
      ok (self.view key, ⟨putEntries self.entries key value⟩) := by
  simp only [insertContents, insertWith_exact _ eqLaw, bind_tc_ok, view]

theorem insertContents_spec [DecidableEq K] (eq : core.cmp.Eq K)
    (eqLaw : ExactEq eq.partialEqInst.eq) (self : HashMap K V S A) (key : K) (value : V)
    (valid : self.WellFormed) :
    ∃ updated : HashMap K V S A,
      insertContents eq self key value = ok (self.view key, updated) ∧
      updated.WellFormed ∧ updated.view key = some value ∧
      ∀ query, query ≠ key → updated.view query = self.view query := by
  refine ⟨⟨putEntries self.entries key value⟩, insertContents_exact eq eqLaw self key value,
    putEntries_nodup self.entries key value valid, ?_, ?_⟩
  · exact lookupEntries_put_same self.entries key value
  · exact fun query different => lookupEntries_put_other self.entries key query value different

theorem eraseEntries_sublist [DecidableEq Q] (keyView : K → Q)
    (entries : List (K × V)) (query : Q) :
    (eraseEntries keyView entries query).Sublist entries := by
  induction entries with
  | nil => exact List.Sublist.refl []
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      by_cases found : query = keyView stored
      · simpa [eraseEntries, found] using (List.Sublist.refl rest).cons (stored, value)
      · simpa [eraseEntries, found] using ih.cons_cons (stored, value)

theorem eraseEntries_nodup [DecidableEq Q] (keyView : K → Q)
    (entries : List (K × V)) (query : Q) (unique : (entries.map Prod.fst).Nodup) :
    ((eraseEntries keyView entries query).map Prod.fst).Nodup :=
  ((eraseEntries_sublist keyView entries query).map Prod.fst).nodup unique

theorem eraseEntries_absent [DecidableEq Q] (keyView : K → Q)
    (entries : List (K × V)) (query : Q)
    (absent : lookupEntries (entries.map fun p => (keyView p.1, p.2)) query = none) :
    eraseEntries keyView entries query = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      by_cases found : query = keyView stored
      · simp [lookupEntries, found] at absent
      · simp only [List.map_cons, lookupEntries, if_neg found] at absent
        simp [eraseEntries, found, ih absent]

theorem lookupEntries_erase_same [DecidableEq Q] (keyView : K → Q)
    (entries : List (K × V)) (query : Q)
    (unique : (entries.map fun p => keyView p.1).Nodup) :
    lookupEntries ((eraseEntries keyView entries query).map
      fun p => (keyView p.1, p.2)) query = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      have h := List.nodup_cons.mp unique
      by_cases found : query = keyView stored
      · simp only [eraseEntries, if_pos found]
        rw [lookupEntries_none_iff]
        simpa [List.map_map, found] using h.1
      · simpa [eraseEntries, found, lookupEntries] using ih h.2

theorem lookupEntries_erase_other [DecidableEq Q] (keyView : K → Q)
    (entries : List (K × V)) (query other : Q) (different : other ≠ query) :
    lookupEntries ((eraseEntries keyView entries query).map
      fun p => (keyView p.1, p.2)) other =
    lookupEntries (entries.map fun p => (keyView p.1, p.2)) other := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      by_cases found : query = keyView stored
      · have otherAbsent : other ≠ keyView stored := by simpa [← found] using different
        simp [eraseEntries, found, lookupEntries, otherAbsent]
      · by_cases otherFound : other = keyView stored <;>
          simp [eraseEntries, found, lookupEntries, otherFound, ih]

theorem removeWith_exact [DecidableEq Q]
    (borrow : K → Result Q) (keyView : K → Q) (eq : Q → Q → Result Bool)
    (borrowLaw : ExactBorrow borrow keyView) (eqLaw : ExactEq eq)
    (entries : List (K × V)) (query : Q) :
    removeWith borrow eq entries query =
      ok (lookupEntries (entries.map fun p => (keyView p.1, p.2)) query,
        eraseEntries keyView entries query) := by
  unfold ExactBorrow at borrowLaw
  unfold ExactEq at eqLaw
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      simp only [removeWith, borrowLaw, eqLaw, bind_tc_ok, decide_eq_true_eq,
        List.map_cons, lookupEntries, eraseEntries]
      split <;> simp_all only [bind_tc_ok]

theorem removeContents_exact [DecidableEq Q] (borrow : core.borrow.Borrow K Q)
    (eq : core.cmp.Eq Q) (keyView : K → Q)
    (borrowLaw : ExactBorrow borrow.borrow keyView) (eqLaw : ExactEq eq.partialEqInst.eq)
    (self : HashMap K V S A) (query : Q) :
    removeContents borrow eq self query =
      ok (lookupEntries (self.entries.map fun p => (keyView p.1, p.2)) query,
        ⟨eraseEntries keyView self.entries query⟩) := by
  simp only [removeContents, removeWith_exact _ keyView _ borrowLaw eqLaw, bind_tc_ok]

theorem removeContents_identity [DecidableEq K] (eq : core.cmp.Eq K)
    (eqLaw : ExactEq eq.partialEqInst.eq) (self : HashMap K V S A) (key : K) :
    removeContents (core.borrow.Borrow.Blanket K) eq self key =
      ok (self.view key, ⟨eraseEntries id self.entries key⟩) := by
  have h := removeContents_exact (core.borrow.Borrow.Blanket K) eq id (by intro; rfl)
    eqLaw self key
  simpa [view] using h

/-- Borrowed-key law: the removed value is the previous lookup, all other borrowed
keys are unchanged, and stored keys stay unique. Distinct stored keys must have
 distinct borrowed views, as required by Rust's compatible Eq/Hash contract. -/
theorem removeContents_spec [DecidableEq Q] (borrow : core.borrow.Borrow K Q)
    (eq : core.cmp.Eq Q) (keyView : K → Q)
    (borrowLaw : ExactBorrow borrow.borrow keyView) (eqLaw : ExactEq eq.partialEqInst.eq)
    (self : HashMap K V S A) (query : Q) (valid : self.WellFormed)
    (borrowedUnique : (self.entries.map fun p => keyView p.1).Nodup) :
    ∃ updated : HashMap K V S A,
      removeContents borrow eq self query =
        ok (lookupEntries (self.entries.map fun p => (keyView p.1, p.2)) query, updated) ∧
      updated.WellFormed ∧
      lookupEntries (updated.entries.map fun p => (keyView p.1, p.2)) query = none ∧
      ∀ other, other ≠ query →
        lookupEntries (updated.entries.map fun p => (keyView p.1, p.2)) other =
        lookupEntries (self.entries.map fun p => (keyView p.1, p.2)) other := by
  refine ⟨⟨eraseEntries keyView self.entries query⟩,
    removeContents_exact borrow eq keyView borrowLaw eqLaw self query,
    eraseEntries_nodup keyView self.entries query valid,
    lookupEntries_erase_same keyView self.entries query borrowedUnique, ?_⟩
  exact fun other different => lookupEntries_erase_other keyView self.entries query other different

theorem removeContents_identity_spec [DecidableEq K] (eq : core.cmp.Eq K)
    (eqLaw : ExactEq eq.partialEqInst.eq) (self : HashMap K V S A) (key : K)
    (valid : self.WellFormed) :
    ∃ updated : HashMap K V S A,
      removeContents (core.borrow.Borrow.Blanket K) eq self key = ok (self.view key, updated) ∧
      updated.WellFormed ∧ updated.view key = none ∧
      ∀ other, other ≠ key → updated.view other = self.view other := by
  simpa [view] using removeContents_spec (core.borrow.Borrow.Blanket K) eq id
    (by intro; rfl) eqLaw self key valid valid

theorem removeContents_absent [DecidableEq Q] (borrow : core.borrow.Borrow K Q)
    (eq : core.cmp.Eq Q) (keyView : K → Q)
    (borrowLaw : ExactBorrow borrow.borrow keyView) (eqLaw : ExactEq eq.partialEqInst.eq)
    (self : HashMap K V S A) (query : Q)
    (absent : lookupEntries (self.entries.map fun p => (keyView p.1, p.2)) query = none) :
    removeContents borrow eq self query = ok (none, self) := by
  rw [removeContents_exact borrow eq keyView borrowLaw eqLaw, absent,
    eraseEntries_absent keyView self.entries query absent]

/-- Callback errors and divergence propagate without inventing a successful update. -/
theorem removeWith_borrow_fail (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query : Q) (error : Error)
    (failed : borrow stored = fail error) :
    removeWith borrow eq ((stored, value) :: rest) query = fail error := by
  simp only [removeWith, failed, bind_tc_fail]

theorem removeWith_borrow_div (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query : Q)
    (diverged : borrow stored = div) :
    removeWith borrow eq ((stored, value) :: rest) query = div := by
  simp only [removeWith, diverged, bind_tc_div]

theorem removeWith_eq_fail (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query borrowed : Q) (error : Error)
    (borrowedOk : borrow stored = ok borrowed) (failed : eq query borrowed = fail error) :
    removeWith borrow eq ((stored, value) :: rest) query = fail error := by
  simp only [removeWith, borrowedOk, failed, bind_tc_ok, bind_tc_fail]

theorem removeWith_eq_div (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query borrowed : Q)
    (borrowedOk : borrow stored = ok borrowed) (diverged : eq query borrowed = div) :
    removeWith borrow eq ((stored, value) :: rest) query = div := by
  simp only [removeWith, borrowedOk, diverged, bind_tc_ok, bind_tc_div]

theorem defaultContents_empty (K V : Type) {S : Type}
    (defaultS : core.default.Default S) (seed : S) (success : defaultS.default = ok seed) :
    defaultContents K V defaultS = ok ⟨[]⟩ := by
  simp only [defaultContents, success, bind_tc_ok]

theorem defaultContents_fail (K V : Type) {S : Type}
    (defaultS : core.default.Default S) (error : Error) (failed : defaultS.default = fail error) :
    defaultContents K V defaultS = fail error := by
  simp only [defaultContents, failed, bind_tc_fail]

theorem defaultContents_div (K V : Type) {S : Type}
    (defaultS : core.default.Default S) (diverged : defaultS.default = div) :
    defaultContents K V defaultS = div := by
  simp only [defaultContents, diverged, bind_tc_div]

/-- Callback failures are preserved even outside the total-callback domain. -/
theorem lookupWith_borrow_fail (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query : Q) (error : Error)
    (failed : borrow stored = fail error) :
    lookupWith borrow eq ((stored, value) :: rest) query = fail error := by
  simp only [lookupWith, failed, bind_tc_fail]

theorem lookupWith_borrow_div (borrow : K → Result Q) (eq : Q → Q → Result Bool)
    (stored : K) (value : V) (rest : List (K × V)) (query : Q)
    (diverged : borrow stored = div) :
    lookupWith borrow eq ((stored, value) :: rest) query = div := by
  simp only [lookupWith, diverged, bind_tc_div]

theorem insertWith_eq_fail (eq : K → K → Result Bool) (stored key : K)
    (old value : V) (rest : List (K × V)) (error : Error)
    (failed : eq key stored = fail error) :
    insertWith eq ((stored, old) :: rest) key value = fail error := by
  simp only [insertWith, failed, bind_tc_fail]

theorem insertWith_eq_div (eq : K → K → Result Bool) (stored key : K)
    (old value : V) (rest : List (K × V)) (diverged : eq key stored = div) :
    insertWith eq ((stored, old) :: rest) key value = div := by
  simp only [insertWith, diverged, bind_tc_div]

end HashMap

/-- Unfiltered constructor spelling retained for direct generated-code use. -/
@[expose]
def HashMapKVSGlobal.Insts.CoreDefaultDefault.default (K V : Type) {S : Type}
    (defaultS : core.default.Default S) : Result (HashMap K V S Global) := do
  HashMap.defaultContents K V defaultS

end std.collections.hash.map

@[expose, rust_fun "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.default (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

@[simp] theorem alloc.vec.Vec.default_eq_new (T : Type) :
    alloc.vec.Vec.default T = ok (alloc.vec.Vec.new T) := rfl

end Aeneas.Std
