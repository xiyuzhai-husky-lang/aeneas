module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.Vec
public section

namespace Aeneas.Std

open Result

@[expose, rust_type "alloc::vec::into_iter::IntoIter" (keepParams := [true, false])]
def alloc.vec.into_iter.IntoIter (T : Type) : Type := alloc.vec.Vec T

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::next"
  (keepParams := [true, false])]
def alloc.vec.into_iter.IteratorIntoIter.next {T : Type} (it: alloc.vec.into_iter.IntoIter T) :
  Result ((Option T) × (alloc.vec.into_iter.IntoIter T)) :=
  match h : it.val with
  | []  => ok (none, it)
  | hd :: tl => ok (hd, .from tl (by grind) )

/-- Value-level model of the pinned IntoIter::fold override (into_iter.rs:367).
Both native ZST and non-ZST branches visit remaining elements in forward order,
update the cursor before calling f, and preserve the mutable callback state.
Pointer validity, destruction, and deallocation remain library-model boundaries. -/
def alloc.vec.into_iter.IteratorIntoIter.foldList
    {T B F : Type} (FnMutInst : core.ops.function.FnMut F (B × T) B)
    (items : List T) (acc : B) (f : F) : Result B :=
  match items with
  | [] => .ok acc
  | item :: rest => do
    let (acc, f) ← FnMutInst.call_mut f (acc, item)
    alloc.vec.into_iter.IteratorIntoIter.foldList FnMutInst rest acc f

/-- Full callback-state specification, including failures and divergence. -/
theorem alloc.vec.into_iter.IteratorIntoIter.foldList_eq_foldlM
    {T B F : Type} (fnm : core.ops.function.FnMut F (B × T) B)
    (items : List T) (acc : B) (f : F) :
    alloc.vec.into_iter.IteratorIntoIter.foldList fnm items acc f = (do
      let state ← items.foldlM (fun state item => fnm.call_mut state.2 (state.1, item))
        (acc, f)
      .ok state.1) := by
  induction items generalizing acc f with
  | nil => simp [alloc.vec.into_iter.IteratorIntoIter.foldList, List.foldlM_nil]
  | cons item rest ih =>
    simp only [alloc.vec.into_iter.IteratorIntoIter.foldList, List.foldlM_cons]
    rw [bind_assoc]
    congr 1
    funext state
    exact ih state.1 state.2

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::fold"
  (keepParams := [true, false, true, true])]
def alloc.vec.into_iter.IteratorIntoIter.fold
    {T B F : Type} (FnMutInst : core.ops.function.FnMut F (B × T) B)
    (iter : alloc.vec.into_iter.IntoIter T) (acc : B) (f : F) : Result B :=
  alloc.vec.into_iter.IteratorIntoIter.foldList FnMutInst iter.val acc f

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>"
  (keepParams := [true, false])]
impl_def core.iter.traits.iterator.IteratorVecIntoIter (T : Type) :
  core.iter.traits.iterator.Iterator (alloc.vec.into_iter.IntoIter T) T := {
  next := alloc.vec.into_iter.IteratorIntoIter.next
  fold := alloc.vec.into_iter.IteratorIntoIter.fold
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorVecIntoIter T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorVecIntoIter T)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.iter.traits.iterator.IteratorVecIntoIter T)
}


/-- Value-level model of native IntoIter::next_back (into_iter.rs:446).
The non-ZST branch decrements end before reading; the ZST branch decrements the
remaining byte-count then reads the aligned start pointer. Both yield the last
remaining value and remove exactly one item. Unsafe pointer validity, aliasing,
destruction and deallocation remain the existing Vec library-model boundary. -/
@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::double_ended::DoubleEndedIterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::next_back"
  (keepParams := [true, false])]
def alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back {T : Type}
    (it : alloc.vec.into_iter.IntoIter T) :
    Result (Option T × alloc.vec.into_iter.IntoIter T) :=
  ok (it.val.getLast?, alloc.vec.Vec.from it.val.dropLast
    (by have := it.property; simp only [List.length_dropLast]; omega))

/-- The actual DoubleEndedIterator::rfold default (double_ended.rs:356), not a
fallback for an override. IntoIter does not override this method. -/
@[expose, trait_default, rust_fun "core::iter::traits::double_ended::DoubleEndedIterator::rfold"]
def core.iter.traits.double_ended.DoubleEndedIterator.rfold.trait_default
    {I Item B F : Type}
    (de : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fn : core.ops.function.FnMut F (B × Item) B)
    (it : I) (acc : B) (f : F) : Result B :=
  core.iter.traits.iterator.Iterator.fold.default de.next_back fn it acc f

@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>"
  (keepParams := [true, false])]
impl_def core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter (T : Type) :
    core.iter.traits.double_ended.DoubleEndedIterator (alloc.vec.into_iter.IntoIter T) T := {
  iteratorInst := core.iter.traits.iterator.IteratorVecIntoIter T
  next_back := alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back
  rfold := core.iter.traits.iterator.Iterator.fold.default
    alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back
}

namespace VecReversePrototype

theorem next_back_contents {T : Type} (it : alloc.vec.into_iter.IntoIter T) :
    ∃ item rest, alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back it = ok (item, rest) ∧
      item = it.val.getLast? ∧ rest.val = it.val.dropLast := by
  exact ⟨_, _, rfl, rfl, alloc.vec.Vec.from_val _ _⟩

theorem next_back_empty {T : Type} (it : alloc.vec.into_iter.IntoIter T)
    (h : it.val = []) :
    alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back it = ok (none, it) := by
  simp only [alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back, h,
    List.getLast?_nil, List.dropLast_nil]
  congr 2
  apply alloc.vec.Vec.ext
  simp [h]

theorem next_back_concat {T : Type} (it : alloc.vec.into_iter.IntoIter T)
    (front : List T) (last : T) (h : it.val = front ++ [last]) :
    ∃ rest, alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back it = ok (some last, rest) ∧
      rest.val = front := by
  refine ⟨alloc.vec.Vec.from it.val.dropLast (by have := it.property; simp; omega), ?_, ?_⟩
  · simp [alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back, h]
  · simp [h]

-- Finite-list induction proves that the actual inherited default, using the
-- modeled next_back, preserves the full Result computation and closure state.
theorem rfold_eq_reverse_foldList {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (acc : B) (f : F) :
    core.iter.traits.iterator.Iterator.fold.default
      alloc.vec.into_iter.DoubleEndedIteratorIntoIter.next_back fn it acc f =
      alloc.vec.into_iter.IteratorIntoIter.foldList fn it.val.reverse acc f := by
  generalize hr : it.val.reverse = items
  induction items generalizing it acc f with
  | nil =>
    have hv : it.val = [] := by simpa using congrArg List.reverse hr
    rw [core.iter.traits.iterator.Iterator.fold.default_none _ fn it it acc f
      (next_back_empty it hv)]
    rfl
  | cons last tail ih =>
    have hv : it.val = tail.reverse ++ [last] := by
      simpa using congrArg List.reverse hr
    obtain ⟨rest, hnext, hrest⟩ := next_back_concat it tail.reverse last hv
    rw [core.iter.traits.iterator.Iterator.fold.default]
    simp only [hnext, bind_tc_ok, alloc.vec.into_iter.IteratorIntoIter.foldList]
    congr 1
    funext state
    exact ih rest state.1 state.2 (by simp [hrest])

theorem rfold_eq_reverse_foldlM {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (acc : B) (f : F) :
    (core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter T).rfold fn it acc f = (do
      let state ← it.val.reverse.foldlM
        (fun (state : B × F) item => fn.call_mut state.2 (state.1, item)) (acc, f)
      ok state.1) := by
  exact (rfold_eq_reverse_foldList fn it acc f).trans
    (alloc.vec.into_iter.IteratorIntoIter.foldList_eq_foldlM fn it.val.reverse acc f)


theorem rfold_empty {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (acc : B) (f : F) (h : it.val = []) :
    (core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter T).rfold fn it acc f = ok acc := by
  change core.iter.traits.iterator.Iterator.fold.default _ _ _ _ _ = _
  rw [rfold_eq_reverse_foldList, h]
  rfl

theorem rfold_callback_fail {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (front : List T) (last : T)
    (acc : B) (f : F) (error : Error) (h : it.val = front ++ [last])
    (hf : fn.call_mut f (acc, last) = fail error) :
    (core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter T).rfold fn it acc f =
      fail error := by
  change core.iter.traits.iterator.Iterator.fold.default _ _ _ _ _ = _
  rw [rfold_eq_reverse_foldList, h]
  simp [alloc.vec.into_iter.IteratorIntoIter.foldList, hf]

theorem rfold_callback_div {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (front : List T) (last : T)
    (acc : B) (f : F) (h : it.val = front ++ [last])
    (hf : fn.call_mut f (acc, last) = .div) :
    (core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter T).rfold fn it acc f = .div := by
  change core.iter.traits.iterator.Iterator.fold.default _ _ _ _ _ = _
  rw [rfold_eq_reverse_foldList, h]
  simp [alloc.vec.into_iter.IteratorIntoIter.foldList, hf]

theorem rfold_callback_state {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : alloc.vec.into_iter.IntoIter T) (front : List T) (last : T)
    (acc acc' : B) (f f' : F) (h : it.val = front ++ [last])
    (hf : fn.call_mut f (acc, last) = ok (acc', f')) :
    (core.iter.traits.double_ended.DoubleEndedIteratorVecIntoIter T).rfold fn it acc f =
      alloc.vec.into_iter.IteratorIntoIter.foldList fn front.reverse acc' f' := by
  change core.iter.traits.iterator.Iterator.fold.default _ _ _ _ _ = _
  rw [rfold_eq_reverse_foldList, h]
  simp [alloc.vec.into_iter.IteratorIntoIter.foldList, hf]

end VecReversePrototype

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>}::into_iter"
  (keepParams := [true, false])]
def alloc.vec.IntoIteratorVec.into_iter {T : Type} (v: alloc.vec.Vec T) : Result (alloc.vec.into_iter.IntoIter T) := ok v

@[expose, reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<alloc::vec::Vec<@T>, @T, alloc::vec::into_iter::IntoIter<@T, @A>>"
  (keepParams := [true, false])]
def core.iter.traits.collect.IntoIteratorVec (T : Type) :
  core.iter.traits.collect.IntoIterator (alloc.vec.Vec T) T
  (alloc.vec.into_iter.IntoIter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorVecIntoIter T
  into_iter := alloc.vec.IntoIteratorVec.into_iter
}

/-- Iterate and collect elements into a list -/
def alloc.vec.FromIteratorVec.iterToList
    {T : Type} {IntoIter : Type}
    (iterInst : core.iter.traits.iterator.Iterator IntoIter T)
    (iter : IntoIter) (acc : List T) : Result (List T) := do
  let (opt, iter) ← iterInst.next iter
  match opt with
  | none => .ok acc.reverse
  | some item => alloc.vec.FromIteratorVec.iterToList iterInst iter (item :: acc)
partial_fixpoint

@[expose, rust_fun
  "alloc::vec::{core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>}::from_iter"]
def alloc.vec.FromIteratorVec.from_iter
  {T : Type} {I : Type} {IntoIter : Type}
  (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter) :
  I → Result (alloc.vec.Vec T) :=
  fun input => do
    let iter ← IntoIteratorInst.into_iter input
    let list ← alloc.vec.FromIteratorVec.iterToList IntoIteratorInst.iteratorInst iter []
    if h : list.length ≤ Usize.max then .ok (.from list h)
    else .fail .panic

@[expose, reducible, rust_trait_impl
  "core::iter::traits::collect::FromIterator<alloc::vec::Vec<@T>, @T>"]
def core.iter.traits.collect.FromIteratorVec (T : Type) :
  core.iter.traits.collect.FromIterator (alloc.vec.Vec T) T := {
  from_iter := fun {I : Type} {IntoIter : Type}
    (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter) =>
    alloc.vec.FromIteratorVec.from_iter IntoIteratorInst
}

@[expose, rust_fun
  "alloc::vec::into_iter::{core::iter::traits::iterator::Iterator<alloc::vec::into_iter::IntoIter<@T, @A>, @T>}::map"]
def alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map
  {T : Type} {A : Type} {F : Type}
  (_FnMutInst : core.ops.function.FnMut F T A) :
  alloc.vec.into_iter.IntoIter T → F →
  Result (core.iter.adapters.map.Map (alloc.vec.into_iter.IntoIter T) F) :=
  fun it f => .ok ⟨ it, f ⟩


end Aeneas.Std
