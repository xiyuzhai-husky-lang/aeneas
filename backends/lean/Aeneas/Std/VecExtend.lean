module
public import Aeneas.Std.ArrayIter
@[expose] public section

namespace Aeneas.Std
open Result

/-- Contents model of the native extension loop: advance the owned iterator,
then append that item before asking for another. Iterator failure/divergence and
modeled vector-size failure propagate immediately. Allocation, specialization,
size-hint calls and Drop behavior remain the existing library-model boundary. -/
def alloc.vec.Vec.extendLoop {T I : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (self : alloc.vec.Vec T) (it : I) : Result (alloc.vec.Vec T) := do
  let (item, rest) ← iterator.next it
  match item with
  | none => ok self
  | some item =>
    let self ← self.push item
    alloc.vec.Vec.extendLoop iterator self rest
partial_fixpoint

@[rust_fun "alloc::vec::{core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, @T>}::extend"
  (keepParams := [true, false, true, true])]
def alloc.vec.Vec.extend {T I IntoIter : Type}
    (into : core.iter.traits.collect.IntoIterator I T IntoIter)
    (self : alloc.vec.Vec T) (input : I) : Result (alloc.vec.Vec T) := do
  let it ← into.into_iter input
  alloc.vec.Vec.extendLoop into.iteratorInst self it

@[reducible, rust_trait_impl "core::iter::traits::collect::Extend<alloc::vec::Vec<@T>, @T>"
  (keepParams := [true, false])]
def core.iter.traits.collect.ExtendVec (T : Type) :
    core.iter.traits.collect.Extend (alloc.vec.Vec T) T where
  extend := alloc.vec.Vec.extend

namespace VecExtension

theorem loop_done {T I : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (self : alloc.vec.Vec T) (it rest : I)
    (h : iterator.next it = ok (none, rest)) :
    alloc.vec.Vec.extendLoop iterator self it = ok self := by
  rw [alloc.vec.Vec.extendLoop]
  simp only [h, bind_tc_ok]

theorem loop_step {T I : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (self updated : alloc.vec.Vec T) (it rest : I) (item : T)
    (hnext : iterator.next it = ok (some item, rest))
    (hpush : self.push item = ok updated) :
    alloc.vec.Vec.extendLoop iterator self it =
      alloc.vec.Vec.extendLoop iterator updated rest := by
  rw [alloc.vec.Vec.extendLoop]
  simp only [hnext, bind_tc_ok, hpush]

theorem loop_next_fail {T I : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (self : alloc.vec.Vec T) (it : I) (err : Error)
    (h : iterator.next it = fail err) :
    alloc.vec.Vec.extendLoop iterator self it = fail err := by
  rw [alloc.vec.Vec.extendLoop]
  simp [h]

theorem loop_next_div {T I : Type}
    (iterator : core.iter.traits.iterator.Iterator I T)
    (self : alloc.vec.Vec T) (it : I)
    (h : iterator.next it = div) :
    alloc.vec.Vec.extendLoop iterator self it = div := by
  rw [alloc.vec.Vec.extendLoop]
  simp [h]

theorem array_loop_exact {T : Type} {N : Usize}
    (self : alloc.vec.Vec T) (it : core.array.iter.IntoIter T N)
    (capacity : self.val.length + it.remaining.length ≤ Usize.max) :
    ∃ updated, alloc.vec.Vec.extendLoop
      (core.iter.traits.iterator.IteratorArrayIntoIter T N) self it = ok updated ∧
      updated.val = self.val ++ it.remaining := by
  generalize hi : it.remaining = items
  induction items generalizing it self with
  | nil =>
    refine ⟨self, ?_, by simp⟩
    exact loop_done _ self it it (ArrayIterator.next_empty it hi)
  | cons item tail ih =>
    obtain ⟨rest, hnext, hrest⟩ := ArrayIterator.next_cons it item tail hi
    have room : self.val.length < Usize.max := by
      simp only [hi, List.length_cons] at capacity
      omega
    obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec self item room)
    have roomRest : pushed.val.length + rest.remaining.length ≤ Usize.max := by
      simp only [hpushed, hrest, List.length_append, List.length_singleton]
      simp only [hi, List.length_cons] at capacity
      omega
    obtain ⟨updated, hloop, hcontents⟩ := ih pushed rest roomRest hrest
    refine ⟨updated, ?_, ?_⟩
    · rw [loop_step _ self pushed it rest item hnext hpush]
      exact hloop
    · simpa [hi, hpushed, hrest, List.append_assoc] using hcontents

theorem array_exact {T : Type} {N : Usize}
    (self : alloc.vec.Vec T) (array : Array T N)
    (capacity : self.val.length + N.val ≤ Usize.max) :
    ∃ updated, alloc.vec.Vec.extend
      (core.iter.traits.collect.IntoIteratorArray T N) self array = ok updated ∧
      updated.val = self.val ++ array.val := by
  obtain ⟨it, hinto, hitems⟩ := ArrayIterator.into_iter_contents array
  have room : self.val.length + it.remaining.length ≤ Usize.max := by
    simpa [hitems] using capacity
  obtain ⟨updated, hloop, hcontents⟩ := array_loop_exact self it room
  refine ⟨updated, ?_, by simpa [hitems] using hcontents⟩
  simp only [alloc.vec.Vec.extend, hinto, bind_tc_ok]
  exact hloop

end VecExtension
end Aeneas.Std
