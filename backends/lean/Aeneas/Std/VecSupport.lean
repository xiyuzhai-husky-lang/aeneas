module
public import Aeneas.Std.Vec
public import Aeneas.Std.IteratorOps
public section

namespace Aeneas.Std
open Result WP

/-- Default Vec constructs the same empty vector as Vec::new. -/
@[expose, rust_fun "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.VecDefault.default (T : Type) : Result (alloc.vec.Vec T) := .ok (alloc.vec.Vec.new T)

@[expose, reducible, rust_trait_impl "core::default::Default<alloc::vec::Vec<@T>>"]
def core.default.DefaultVec (T : Type) : core.default.Default (alloc.vec.Vec T) := {
  default := alloc.vec.VecDefault.default T
}

/-- Like with_capacity, reserve models logical contents, not allocator capacity.
    The length-plus-additional arithmetic overflow is still checked. -/
@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::reserve" (keepParams := [true, false])]
def alloc.vec.Vec.reserve {T : Type} (self : alloc.vec.Vec T) (additional : Usize) :
    Result (alloc.vec.Vec T) :=
  if self.val.length + additional.val ≤ Usize.max then .ok self else .fail .panic

/-- Extension reads the iterator in order and checks each actual logical push.
    Infinite iterators do not receive an artificial termination bound. -/
def alloc.vec.Vec.extendIterator {T Iter : Type}
    (iter : core.iter.traits.iterator.Iterator Iter T) (self : alloc.vec.Vec T) (state : Iter) :
    Result (alloc.vec.Vec T) := do
  let (value, next) ← iter.next state
  match value with
  | none => .ok self
  | some value =>
    let self ← alloc.vec.Vec.push self value
    alloc.vec.Vec.extendIterator iter self next
partial_fixpoint

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, @T>}::extend"
  (keepParams := [true, false, true, true])]
def alloc.vec.Vec.extend {T I Iter : Type}
    (into : core.iter.traits.collect.IntoIterator I T Iter) (self : alloc.vec.Vec T) (input : I) :
    Result (alloc.vec.Vec T) := do
  let state ← into.into_iter input
  alloc.vec.Vec.extendIterator into.iteratorInst self state

/-- A finite exact trace derived from an iterator's concrete next function. -/
inductive IteratorTrace {T I : Type} (iter : core.iter.traits.iterator.Iterator I T) : I → List T → Prop where
  | done {s next} (he : iter.next s = .ok (none, next)) : IteratorTrace iter s []
  | step {s next x xs} (he : iter.next s = .ok (some x, next))
      (tail : IteratorTrace iter next xs) : IteratorTrace iter s (x :: xs)

/-- Finite concrete iteration and initial append room imply total extension,
    retaining exact element order; future extend success is not a premise. -/
theorem alloc.vec.Vec.extend_finite {T I : Type} (iter : core.iter.traits.iterator.Iterator I T)
    {s : I} {xs : List T} (ht : IteratorTrace iter s xs) (v : alloc.vec.Vec T)
    (hroom : v.val.length + xs.length ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extendIterator iter v s = .ok w ∧ w.val = v.val ++ xs := by
  induction ht generalizing v with
  | done he =>
    refine ⟨v, ?_, by simp only [List.append_nil]⟩
    rw [alloc.vec.Vec.extendIterator]
    simp only [he, bind_tc_ok]
  | @step s next x xs he ht ih =>
    obtain ⟨mid, hm, hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec v x (by simp only [List.length_cons] at hroom; scalar_tac))
    have room : mid.val.length + xs.length ≤ Usize.max := by
      rw [hval, List.length_append, List.length_singleton]
      simp only [List.length_cons] at hroom
      scalar_tac
    obtain ⟨w, hw, hv⟩ := ih mid room
    refine ⟨w, ?_, ?_⟩
    · rw [alloc.vec.Vec.extendIterator]
      simp only [he, hm, bind_tc_ok]
      exact hw
    · rw [hv, hval, List.append_assoc]
      rfl

/-- The bounded repeat adapter has an actual finite trace, even though the
    underlying repeat iterator remains infinite. -/
theorem IteratorTrace.take_repeat_aux {T : Type} (clone : core.clone.Clone T) (x : T)
    (hc : clone.clone x = .ok x) (fuel : Nat) :
    ∀ n : Usize, n.val = fuel → IteratorTrace
      (core.iter.traits.iterator.IteratorTake (core.iter.traits.iterator.IteratorRepeat clone))
      ⟨⟨x⟩, n⟩ (List.replicate n.val x) := by
  induction fuel with
  | zero =>
    intro n hn
    rw [hn, List.replicate_zero]
    refine IteratorTrace.done (next := ⟨⟨x⟩, n⟩) ?_
    simp only [core.iter.adapters.take.IteratorTake.next,
      hn, ite_true]
  | succ fuel ih =>
    intro n hn
    have hpositive : n.val ≠ 0 := by scalar_tac
    obtain ⟨prev, hsub, hp⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := n) (y := 1#usize) (by scalar_tac))
    have hprev : prev.val = fuel := by scalar_tac
    have hstep :
        (core.iter.traits.iterator.IteratorTake (core.iter.traits.iterator.IteratorRepeat clone)).next
          ⟨⟨x⟩, n⟩ = .ok (some x, ⟨⟨x⟩, prev⟩) := by
      simp only [core.iter.adapters.take.IteratorTake.next,
        hpositive, ite_false, hsub,
        core.iter.sources.repeat.IteratorRepeat.next, hc, bind_tc_ok]
    have ht := IteratorTrace.step hstep (ih prev hprev)
    simpa only [hn, hprev, List.replicate_succ] using ht

/-- Repeating exactly n elements and extending checks every push and terminates
    with the exact replicated suffix, under only initial append room. -/
theorem alloc.vec.Vec.extend_repeat_take {T : Type} (clone : core.clone.Clone T) (x : T)
    (hc : clone.clone x = .ok x) (n : Usize) (v : alloc.vec.Vec T)
    (hroom : v.val.length + n.val ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extend
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.traits.iterator.IteratorTake (core.iter.traits.iterator.IteratorRepeat clone)))
      v ⟨⟨x⟩, n⟩ = .ok w ∧ w.val = v.val ++ List.replicate n.val x := by
  have ht := IteratorTrace.take_repeat_aux clone x hc n.val n rfl
  obtain ⟨w, hw, hv⟩ := alloc.vec.Vec.extend_finite _ ht v (by simpa only [List.length_replicate] using hroom)
  refine ⟨w, ?_, hv⟩
  simp only [alloc.vec.Vec.extend,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok]
  exact hw


end Aeneas.Std
