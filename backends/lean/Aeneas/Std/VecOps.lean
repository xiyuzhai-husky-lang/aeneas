module
public import Aeneas.Std.Vec
public import Mathlib.Data.List.Destutter

/-!
Logical contents models for Vec operations used by BatSat. As with the existing
Vec model, capacity, allocation/layout failures, destructor effects, and unwinding
are outside this interpretation. Callback computations are retained in Result.
These definitions do not verify the unsafe native Vec implementation.
-/
@[expose] public section
namespace Aeneas.Std
open Result Error WP
namespace alloc.vec.Vec

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::as_slice"
    -canFail -lift (keepParams := [true, false])]
def as_slice {T : Type} (v : alloc.vec.Vec T) : Slice T := v.deref

@[simp] theorem as_slice_val {T : Type} (v : alloc.vec.Vec T) :
    v.as_slice.val = v.val := by simp [as_slice, deref]

theorem as_slice_eq_slice {T : Type} (v : alloc.vec.Vec T) :
    v.as_slice = v.slice := by
  apply Slice.ext
  simp [as_slice, deref, val]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::truncate"
    (keepParams := [true, false])]
def truncate {T : Type} (v : alloc.vec.Vec T) (n : Usize) : Result (alloc.vec.Vec T) :=
  .ok (.from (v.val.take n.val) (by simp))

@[step] theorem truncate_spec {T : Type} (v : alloc.vec.Vec T) (n : Usize) :
    v.truncate n ⦃ w => w.val = v.val.take n.val ∧
      w.length = min n.val v.length ⦄ := by simp [truncate]

theorem truncate_of_length_le {T : Type} (v : alloc.vec.Vec T) (n : Usize)
    (h : v.length ≤ n.val) : v.truncate n = .ok v := by
  simp [truncate, List.take_of_length_le h]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"
    (keepParams := [true, false])]
def remove {T : Type} (v : alloc.vec.Vec T) (i : Usize) : Result (T × alloc.vec.Vec T) :=
  if h : i.val < v.length then
    .ok (v.val[i.val], .from (v.val.eraseIdx i.val)
      ((List.length_eraseIdx_le v.val i.val).trans v.property))
  else .fail .arrayOutOfBounds

@[step] theorem remove_spec {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (h : i.val < v.length) :
    v.remove i ⦃ r => r.1 = v.val[i.val] ∧
      r.2.val = v.val.take i.val ++ v.val.drop (i.val + 1) ∧
      r.2.length = v.length - 1 ⦄ := by
  simp [remove, h, List.eraseIdx_eq_take_drop_succ]
  scalar_tac

theorem remove_out_of_bounds {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (h : v.length ≤ i.val) : v.remove i = .fail .arrayOutOfBounds := by
  simp [remove, Nat.not_lt.mpr h]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"
    (keepParams := [true, false])]
def pop {T : Type} (v : alloc.vec.Vec T) : Result (Option T × alloc.vec.Vec T) :=
  .ok (v.val.getLast?, .from v.val.dropLast
    ((by simp : v.val.dropLast.length ≤ v.val.length).trans v.property))

@[step] theorem pop_spec {T : Type} (v : alloc.vec.Vec T) :
    v.pop ⦃ r => r.1 = v.val.getLast? ∧ r.2.val = v.val.dropLast ∧
      r.2.length = v.length - 1 ⦄ := by simp [pop]

theorem pop_empty {T : Type} : (new T).pop = .ok (none, new T) := by
  simp [pop, new]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"
    (keepParams := [true, false])]
def clear {T : Type} (_v : alloc.vec.Vec T) : Result (alloc.vec.Vec T) := .ok (new T)

@[step] theorem clear_spec {T : Type} (v : alloc.vec.Vec T) :
    v.clear ⦃ w => w.val = [] ⦄ := by simp [clear, new]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"
    -canFail -lift (keepParams := [true, false])]
def is_empty {T : Type} (v : alloc.vec.Vec T) : Bool := v.val.isEmpty

@[simp] theorem is_empty_iff {T : Type} (v : alloc.vec.Vec T) :
    v.is_empty = true ↔ v.val = [] := by simp [is_empty]

/-- The subtype records that filtering preserves order and cannot grow the vector.
    The updated closure is passed to the next call, even when an element is removed. -/
def retainList {T F : Type} (call : F → T → Result (Bool × F)) :
    (xs : List T) → F → Result {ys : List T // ys.Sublist xs}
  | [], _ => .ok ⟨[], .refl []⟩
  | x :: xs, state => do
    let (keep, state) ← call state x
    let ys ← retainList call xs state
    if keep then .ok ⟨x :: ys.val, .cons_cons x ys.property⟩
    else .ok ⟨ys.val, .cons x ys.property⟩

theorem retainList_filter {T F : Type} (call : F → T → Result (Bool × F))
    (p : T → Bool) (xs : List T)
    (hcall : ∀ state x, x ∈ xs → ∃ next, call state x = .ok (p x, next))
    (state : F) :
    retainList call xs state = .ok ⟨xs.filter p, List.filter_sublist⟩ := by
  induction xs generalizing state with
  | nil => simp [retainList]
  | cons x xs ih =>
    obtain ⟨next, hnext⟩ := hcall state x (by simp)
    have htail : ∀ state x, x ∈ xs → ∃ next, call state x = .ok (p x, next) := by
      intro state y hy
      exact hcall state y (by simp [hy])
    cases hp : p x <;> simp [retainList, hnext, ih htail next, hp]

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::retain"
    (keepParams := [true, false, true])]
def retain {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (state : F) : Result (alloc.vec.Vec T) := do
  let ys ← retainList fnMut.call_mut v.val state
  .ok (.from ys.val (ys.property.length_le.trans v.property))

@[step] theorem retain_spec {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (state : F) (p : T → Bool)
    (hcall : ∀ state x, x ∈ v.val → ∃ next, fnMut.call_mut state x = .ok (p x, next)) :
    retain fnMut v state ⦃ w => w.val = v.val.filter p ⦄ := by
  simp [retain, retainList_filter fnMut.call_mut p v.val hcall state]

/-- Compare current against previous retained element, in that order. -/
def dedupFrom {T : Type} (eq : T → T → Result Bool) :
    (prev : T) → (xs : List T) → Result {ys : List T // ys.Sublist (prev :: xs)}
  | prev, [] => .ok ⟨[prev], .refl _⟩
  | prev, current :: xs => do
    let same ← eq current prev
    if same then
      let ys ← dedupFrom eq prev xs
      .ok ⟨ys.val, ys.property.trans (.cons_cons prev (.cons current (.refl xs)))⟩
    else
      let ys ← dedupFrom eq current xs
      .ok ⟨prev :: ys.val, .cons_cons prev ys.property⟩

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::dedup"
    (keepParams := [true, false])]
def dedup {T : Type} (eqInst : core.cmp.PartialEq T T)
    (v : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  match hv : v.val with
  | [] => .ok v
  | prev :: xs => do
    let ys ← dedupFrom eqInst.eq prev xs
    .ok (.from ys.val (ys.property.length_le.trans (by simpa only [hv] using v.property)))

theorem dedupFrom_destutter {T : Type} (eq : T → T → Result Bool)
    (b : T → T → Bool) (hcall : ∀ x y, eq x y = .ok (b x y))
    (prev : T) (xs : List T) :
    dedupFrom eq prev xs = .ok
      ⟨xs.destutter' (fun prev current => b current prev = false) prev,
       xs.destutter'_sublist _ prev⟩ := by
  induction xs generalizing prev with
  | nil => simp [dedupFrom]
  | cons current xs ih =>
    cases hb : b current prev <;>
      simp [dedupFrom, hcall, ih, hb]

@[step] theorem dedup_spec {T : Type} (eqInst : core.cmp.PartialEq T T)
    (v : alloc.vec.Vec T) (b : T → T → Bool)
    (hcall : ∀ x y, eqInst.eq x y = .ok (b x y)) :
    dedup eqInst v ⦃ w =>
      w.val = v.val.destutter (fun prev current => b current prev = false) ∧
      w.val.Sublist v.val ∧
      w.val.IsChain (fun prev current => b current prev = false) ⦄ := by
  unfold dedup
  split <;> rename_i hv
  · simp [hv]
  · simp [dedupFrom_destutter eqInst.eq b hcall, hv,
      List.destutter_cons', List.destutter'_sublist, List.isChain_destutter']

/-- Adjacent duplicate removal preserves membership, even if the input is unsorted. -/
theorem mem_destutterFrom_ne {T : Type} [DecidableEq T] (x prev : T) (xs : List T) :
    x ∈ xs.destutter' (· ≠ ·) prev ↔ x ∈ prev :: xs := by
  induction xs generalizing prev with
  | nil => simp
  | cons current xs ih =>
    by_cases h : prev = current
    · subst current
      simp [ih]
    · simp [h, ih]

theorem mem_destutter_ne {T : Type} [DecidableEq T] (x : T) (xs : List T) :
    x ∈ xs.destutter (· ≠ ·) ↔ x ∈ xs := by
  cases xs with
  | nil => simp
  | cons prev xs => exact mem_destutterFrom_ne x prev xs

@[step] theorem dedup_eq_spec {T : Type} [DecidableEq T]
    (eqInst : core.cmp.PartialEq T T) (v : alloc.vec.Vec T)
    (hcall : ∀ x y, eqInst.eq x y = .ok (decide (x = y))) :
    dedup eqInst v ⦃ w =>
      (∀ x, x ∈ w.val ↔ x ∈ v.val) ∧ w.val.Sublist v.val ∧
      w.val.IsChain (· ≠ ·) ⦄ := by
  have h := dedup_spec eqInst v (fun x y => decide (x = y)) hcall
  apply WP.spec_mono h
  intro w hw
  simp only [decide_eq_false_iff_not] at hw
  simp only [ne_comm] at hw
  rcases hw with ⟨hw, hsub, hchain⟩
  exact ⟨fun x => by rw [hw]; exact mem_destutter_ne x v.val, hsub, hchain⟩

end alloc.vec.Vec
end Aeneas.Std
