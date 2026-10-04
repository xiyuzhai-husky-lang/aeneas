module
public import Aeneas.Std.Vec
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std
open Result WP

/-- `then` consults the tie-breaking ordering only when the first is equal. -/
@[expose, rust_fun "core::cmp::{core::cmp::Ordering}::then"]
def core.cmp.Ordering.then (first second : Ordering) : Result Ordering :=
  .ok (if first = .eq then second else first)

/-- Rust bool ordering puts false before true. -/
@[expose, rust_fun "core::cmp::impls::{core::cmp::Ord<bool>}::cmp"]
def core.cmp.impls.OrdBool.cmp (first second : Bool) : Result Ordering :=
  .ok (match first, second with
    | false, true => .lt
    | true, false => .gt
    | _, _ => .eq)

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"
  (keepParams := [true, false])]
def SharedVec.IntoIterator.into_iter {T : Type} (v : alloc.vec.Vec T) :
    Result (core.slice.iter.Iter T) := core.slice.Slice.iter v.slice

/-- Mutating the borrowed iterator writes the resulting slice back to the Vec. -/
@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a mut alloc::vec::Vec<@T>, &'a mut @T, core::slice::iter::IterMut<'a, @T>>}::into_iter"
  (keepParams := [true, false])]
def MutVec.IntoIterator.into_iter {T : Type} (v : alloc.vec.Vec T) :
    Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → alloc.vec.Vec T)) :=
  .ok (⟨v.slice, 0⟩, fun it => ⟨it.slice⟩)

/-- Slice conversion executes each Clone and uses the existing slice clone model; Clone failure/divergence is retained. -/
@[expose, rust_fun
  "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, &'0 [@T]>}::from"]
def alloc.vec.VecFromSlice.from {T : Type} (clone : core.clone.Clone T) (s : Slice T) :
    Result (alloc.vec.Vec T) :=
  alloc.slice.Slice.to_vec clone s

/-- The exact comparison truth table has no opaque comparison implementation. -/
theorem core.cmp.impls.OrdBool.cmp_correct (a b : Bool) :
    core.cmp.impls.OrdBool.cmp a b = .ok
      (if a = b then .eq else if a = false then .lt else .gt) := by
  cases a <;> cases b <;> rfl

theorem core.cmp.Ordering.then_correct (a b : Ordering) :
    core.cmp.Ordering.then a b = .ok (if a = .eq then b else a) := rfl

/-- Shared iteration starts at the first element with exactly the Vec contents. -/
theorem SharedVec.IntoIterator.into_iter_correct {T : Type} (v : alloc.vec.Vec T) :
    SharedVec.IntoIterator.into_iter v = .ok ⟨v.slice, 0⟩ := rfl

/-- Mutable iteration has the actual initial contents, and its return function
    retains every modification made in the resulting iterator slice. -/
theorem MutVec.IntoIterator.into_iter_correct {T : Type} (v : alloc.vec.Vec T) :
    MutVec.IntoIterator.into_iter v = .ok (⟨v.slice, 0⟩, fun it => ⟨it.slice⟩) := rfl

/-- A real identity Clone trace produces an exact copy, without assuming that
    the enclosing Vec conversion will succeed. -/
theorem alloc.vec.VecFromSlice.from_correct {T : Type}
    (clone : core.clone.Clone T) (s : Slice T)
    (identity : ∀ x ∈ s.val, clone.clone x = .ok x) :
    ∃ v, alloc.vec.VecFromSlice.from clone s = .ok v ∧ v.val = s.val := by
  obtain ⟨v, call, contents⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec clone s identity)
  exact ⟨v, call, congrArg Slice.val contents.symm⟩

end Aeneas.Std
