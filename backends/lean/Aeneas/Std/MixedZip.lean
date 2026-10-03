module
public import Aeneas.Std.SliceZip
public import Aeneas.Std.VecIter
@[expose] public section

open Aeneas Aeneas.Std Result
open SliceZipPrototype (Produces foldWindow defaultFold_of_produces)

namespace MixedZip

-- Generic logical laws over existing Vec and slice models. The dictionaries
-- below are selected only for admitted pinned native instances. Neither these
-- laws nor the conditional bindings prove native unsafe specialization,
-- allocation, callback destruction or Drop correspondence.
def tailVec {A : Type} (v : alloc.vec.into_iter.IntoIter A) :
    alloc.vec.into_iter.IntoIter A :=
  alloc.vec.Vec.from v.val.tail (by have := v.property; simp; omega)

@[simp] theorem tailVec_val {A : Type} (v : alloc.vec.into_iter.IntoIter A) :
    (tailVec v).val = v.val.tail := by simp [tailVec]

theorem vec_next_nil {A : Type} (v : alloc.vec.into_iter.IntoIter A)
    (h : v.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next v = ok (none, v) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i x xs hx
    rw [h] at hx
    contradiction

theorem vec_next_cons {A : Type} (v : alloc.vec.into_iter.IntoIter A)
    (x : A) (xs : List A) (h : v.val = x :: xs) :
    alloc.vec.into_iter.IteratorIntoIter.next v = ok (some x, tailVec v) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i hx
    rw [h] at hx
    contradiction
  · rename_i y ys hy
    have hs : x = y ∧ xs = ys := by simpa [h] using hy
    rcases hs with ⟨rfl, rfl⟩
    congr 2
    apply alloc.vec.Vec.ext
    simp [h]

def sliceVecWindow {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) : List (A × B) :=
  left.remaining.zip right.val

def vecSliceWindow {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) : List (A × B) :=
  left.val.zip right.remaining

def sliceVecNext {A B : Type}
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (alloc.vec.into_iter.IntoIter B)) :=
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorSliceIter A)
    (core.iter.traits.iterator.IteratorVecIntoIter B) z

def vecSliceNext {A B : Type}
    (z : core.iter.adapters.zip.Zip (alloc.vec.into_iter.IntoIter A) (core.slice.iter.Iter B)) :=
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorVecIntoIter A)
    (core.iter.traits.iterator.IteratorSliceIter B) z

theorem sliceVecNext_left_none {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) (h : left.slice.val.length ≤ left.i) :
    sliceVecNext ⟨left, right⟩ = ok (none, ⟨left, right⟩) := by
  simp [sliceVecNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.slice.iter.IteratorSliceIter.next, show ¬ left.i < left.slice.val.length by omega]

theorem sliceVecNext_right_none {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) (hl : left.i < left.slice.val.length)
    (hr : right.val = []) :
    sliceVecNext ⟨left, right⟩ = ok (none, ⟨{left with i := left.i + 1}, right⟩) := by
  simp [sliceVecNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.slice.iter.IteratorSliceIter.next, hl, vec_next_nil right hr]

theorem sliceVecNext_some {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) (x : B) (xs : List B)
    (hl : left.i < left.slice.val.length) (hr : right.val = x :: xs) :
    sliceVecNext ⟨left, right⟩ =
      ok (some (left.slice.val[left.i], x), ⟨{left with i := left.i + 1}, tailVec right⟩) := by
  simp [sliceVecNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.slice.iter.IteratorSliceIter.next, hl, vec_next_cons right x xs hr]
  rfl

theorem vecSliceNext_left_none {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) (h : left.val = []) :
    vecSliceNext ⟨left, right⟩ = ok (none, ⟨left, right⟩) := by
  simp [vecSliceNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    vec_next_nil left h]

theorem vecSliceNext_right_none {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) (x : A) (xs : List A) (hl : left.val = x :: xs)
    (hr : right.slice.val.length ≤ right.i) :
    vecSliceNext ⟨left, right⟩ = ok (none, ⟨tailVec left, right⟩) := by
  simp [vecSliceNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.slice.iter.IteratorSliceIter.next, vec_next_cons left x xs hl,
    show ¬ right.i < right.slice.val.length by omega]

theorem vecSliceNext_some {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) (x : A) (xs : List A)
    (hl : left.val = x :: xs) (hr : right.i < right.slice.val.length) :
    vecSliceNext ⟨left, right⟩ =
      ok (some (x, right.slice.val[right.i]), ⟨tailVec left, {right with i := right.i + 1}⟩) := by
  simp [vecSliceNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    core.slice.iter.IteratorSliceIter.next, hr, vec_next_cons left x xs hl]
  rfl

theorem sliceVecWindow_length {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) :
    (sliceVecWindow left right).length = min (left.slice.val.length - left.i) right.val.length := by
  simp [sliceVecWindow, core.slice.iter.Iter.remaining]

theorem vecSliceWindow_length {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) :
    (vecSliceWindow left right).length = min left.val.length (right.slice.val.length - right.i) := by
  simp [vecSliceWindow, core.slice.iter.Iter.remaining]

theorem sliceVecWindow_pair_at {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) (i : Nat) :
    (sliceVecWindow left right)[i]? = left.slice.val[left.i + i]?.bind
      (fun a => right.val[i]?.map (fun b => (a,b))) := by
  simp [sliceVecWindow, core.slice.iter.Iter.remaining, List.zip, List.getElem?_zipWith', Option.bind_map]

theorem vecSliceWindow_pair_at {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) (i : Nat) :
    (vecSliceWindow left right)[i]? = left.val[i]?.bind
      (fun a => right.slice.val[right.i + i]?.map (fun b => (a,b))) := by
  simp [vecSliceWindow, core.slice.iter.Iter.remaining, List.zip, List.getElem?_zipWith', Option.bind_map]

theorem sliceVec_produces {A B : Type} (left : core.slice.iter.Iter A)
    (right : alloc.vec.into_iter.IntoIter B) :
    Produces sliceVecNext ⟨left, right⟩ (sliceVecWindow left right) := by
  by_cases hl : left.i < left.slice.val.length
  · cases hr : right.val with
    | nil =>
      have hw : sliceVecWindow left right = [] := by simp [sliceVecWindow, hr]
      rw [hw]
      exact Produces.nil _ _ (sliceVecNext_right_none left right hl hr)
    | cons x xs =>
      have hw : sliceVecWindow left right = (left.slice.val[left.i], x) ::
          sliceVecWindow {left with i := left.i + 1} (tailVec right) := by
        simp only [sliceVecWindow, core.slice.iter.Iter.remaining, tailVec_val]
        rw [List.drop_eq_getElem_cons hl, hr]
        rfl
      rw [hw]
      exact Produces.cons _ _ _ _ (sliceVecNext_some left right x xs hl hr)
        (sliceVec_produces _ _)
  · have hn : left.slice.val.length ≤ left.i := by omega
    have hw : sliceVecWindow left right = [] := by
      simp [sliceVecWindow, core.slice.iter.Iter.remaining, List.drop_eq_nil_of_le hn]
    rw [hw]
    exact Produces.nil _ _ (sliceVecNext_left_none left right hn)
termination_by left.slice.val.length - left.i

theorem vecSlice_produces {A B : Type} (left : alloc.vec.into_iter.IntoIter A)
    (right : core.slice.iter.Iter B) :
    Produces vecSliceNext ⟨left, right⟩ (vecSliceWindow left right) := by
  cases hl : left.val with
  | nil =>
    have hw : vecSliceWindow left right = [] := by simp [vecSliceWindow, hl]
    rw [hw]
    exact Produces.nil _ _ (vecSliceNext_left_none left right hl)
  | cons x xs =>
    by_cases hr : right.i < right.slice.val.length
    · have hw : vecSliceWindow left right = (x, right.slice.val[right.i]) ::
          vecSliceWindow (tailVec left) {right with i := right.i + 1} := by
        simp only [vecSliceWindow, core.slice.iter.Iter.remaining, tailVec_val]
        rw [List.drop_eq_getElem_cons hr, hl]
        rfl
      rw [hw]
      exact Produces.cons _ _ _ _ (vecSliceNext_some left right x xs hl hr)
        (vecSlice_produces _ _)
    · have hn : right.slice.val.length ≤ right.i := by omega
      have hw : vecSliceWindow left right = [] := by
        simp [vecSliceWindow, core.slice.iter.Iter.remaining, List.drop_eq_nil_of_le hn]
      rw [hw]
      exact Produces.nil _ _ (vecSliceNext_right_none left right x xs hl hn)
termination_by left.val.length
decreasing_by simp_wf; simp [hl]

def sliceVecFold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : alloc.vec.into_iter.IntoIter B)
    (acc : Acc) (f : F) : Result Acc :=
  foldWindow fn (sliceVecWindow left right) acc f

def vecSliceFold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : alloc.vec.into_iter.IntoIter A) (right : core.slice.iter.Iter B)
    (acc : Acc) (f : F) : Result Acc :=
  foldWindow fn (vecSliceWindow left right) acc f

theorem sliceVecFold_eq_modeled_next {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : alloc.vec.into_iter.IntoIter B)
    (acc : Acc) (f : F) :
    core.iter.traits.iterator.Iterator.fold.default sliceVecNext fn ⟨left, right⟩ acc f =
      sliceVecFold fn left right acc f :=
  defaultFold_of_produces sliceVecNext fn _ _ (sliceVec_produces left right) acc f

theorem vecSliceFold_eq_modeled_next {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : alloc.vec.into_iter.IntoIter A) (right : core.slice.iter.Iter B)
    (acc : Acc) (f : F) :
    core.iter.traits.iterator.Iterator.fold.default vecSliceNext fn ⟨left, right⟩ acc f =
      vecSliceFold fn left right acc f :=
  defaultFold_of_produces vecSliceNext fn _ _ (vecSlice_produces left right) acc f

-- Acc is arbitrary. A native Rust Result stored inside it is an ordinary value;
-- only the outer Aeneas Result computation sequences panic/failure/divergence.
theorem sliceVecFold_callback_step {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : alloc.vec.into_iter.IntoIter B)
    (x : B) (xs : List B) (hl : left.i < left.slice.val.length)
    (hr : right.val = x :: xs) (acc : Acc) (f : F) :
    sliceVecFold fn left right acc f = (do
      let (acc', f') ← fn.call_mut f (acc, (left.slice.val[left.i], x))
      sliceVecFold fn {left with i := left.i + 1} (tailVec right) acc' f') := by
  have hw : sliceVecWindow left right = (left.slice.val[left.i], x) ::
      sliceVecWindow {left with i := left.i + 1} (tailVec right) := by
    simp only [sliceVecWindow, core.slice.iter.Iter.remaining, tailVec_val]
    rw [List.drop_eq_getElem_cons hl, hr]
    rfl
  simp only [sliceVecFold, hw, SliceZipPrototype.foldWindow_cons]

theorem vecSliceFold_callback_step {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : alloc.vec.into_iter.IntoIter A) (right : core.slice.iter.Iter B)
    (x : A) (xs : List A) (hl : left.val = x :: xs)
    (hr : right.i < right.slice.val.length) (acc : Acc) (f : F) :
    vecSliceFold fn left right acc f = (do
      let (acc', f') ← fn.call_mut f (acc, (x, right.slice.val[right.i]))
      vecSliceFold fn (tailVec left) {right with i := right.i + 1} acc' f') := by
  have hw : vecSliceWindow left right = (x, right.slice.val[right.i]) ::
      vecSliceWindow (tailVec left) {right with i := right.i + 1} := by
    simp only [vecSliceWindow, core.slice.iter.Iter.remaining, tailVec_val]
    rw [List.drop_eq_getElem_cons hr, hl]
    rfl
  simp only [vecSliceFold, hw, SliceZipPrototype.foldWindow_cons]

theorem sliceVecFold_callback_fail {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : alloc.vec.into_iter.IntoIter B)
    (x : B) (xs : List B) (hl : left.i < left.slice.val.length) (hr : right.val = x :: xs)
    (acc : Acc) (f : F) (error : Error)
    (h : fn.call_mut f (acc, (left.slice.val[left.i], x)) = fail error) :
    sliceVecFold fn left right acc f = fail error := by
  rw [sliceVecFold_callback_step fn left right x xs hl hr, h]
  simp

theorem sliceVecFold_callback_div {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : alloc.vec.into_iter.IntoIter B)
    (x : B) (xs : List B) (hl : left.i < left.slice.val.length) (hr : right.val = x :: xs)
    (acc : Acc) (f : F)
    (h : fn.call_mut f (acc, (left.slice.val[left.i], x)) = .div) :
    sliceVecFold fn left right acc f = .div := by
  rw [sliceVecFold_callback_step fn left right x xs hl hr, h]
  simp

theorem vecSliceFold_callback_fail {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : alloc.vec.into_iter.IntoIter A) (right : core.slice.iter.Iter B)
    (x : A) (xs : List A) (hl : left.val = x :: xs) (hr : right.i < right.slice.val.length)
    (acc : Acc) (f : F) (error : Error)
    (h : fn.call_mut f (acc, (x, right.slice.val[right.i])) = fail error) :
    vecSliceFold fn left right acc f = fail error := by
  rw [vecSliceFold_callback_step fn left right x xs hl hr, h]
  simp

theorem vecSliceFold_callback_div {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : alloc.vec.into_iter.IntoIter A) (right : core.slice.iter.Iter B)
    (x : A) (xs : List A) (hl : left.val = x :: xs) (hr : right.i < right.slice.val.length)
    (acc : Acc) (f : F)
    (h : fn.call_mut f (acc, (x, right.slice.val[right.i])) = .div) :
    vecSliceFold fn left right acc f = .div := by
  rw [vecSliceFold_callback_step fn left right x xs hl hr, h]
  simp

end MixedZip

namespace Aeneas.Std

/-- Private admitted-instance model; native unsafe specialization and destruction
remain library boundaries, distinct from the generic logical laws above. -/
def core.iter.adapters.zip.SliceVecZip.next {A B : Type}
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (alloc.vec.into_iter.IntoIter B)) :=
  MixedZip.sliceVecNext z

def core.iter.adapters.zip.SliceVecZip.fold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (alloc.vec.into_iter.IntoIter B))
    (acc : Acc) (f : F) : Result Acc := MixedZip.sliceVecFold fn z.fst z.snd acc f

def core.iter.adapters.zip.VecSliceZip.next {A B : Type}
    (z : core.iter.adapters.zip.Zip (alloc.vec.into_iter.IntoIter A) (core.slice.iter.Iter B)) :=
  MixedZip.vecSliceNext z

def core.iter.adapters.zip.VecSliceZip.fold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (z : core.iter.adapters.zip.Zip (alloc.vec.into_iter.IntoIter A) (core.slice.iter.Iter B))
    (acc : Acc) (f : F) : Result Acc := MixedZip.vecSliceFold fn z.fst z.snd acc f

def core.iter.traits.iterator.IteratorSliceVecZip (A B : Type) :
    core.iter.traits.iterator.Iterator
      (core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (alloc.vec.into_iter.IntoIter B)) (A × B) where
  next := core.iter.adapters.zip.SliceVecZip.next
  fold := core.iter.adapters.zip.SliceVecZip.fold
  step_by := core.iter.traits.iterator.Iterator.step_by.default
  enumerate := core.iter.traits.iterator.Iterator.enumerate.default
  take := core.iter.traits.iterator.Iterator.take.default

def core.iter.traits.iterator.IteratorVecSliceZip (A B : Type) :
    core.iter.traits.iterator.Iterator
      (core.iter.adapters.zip.Zip (alloc.vec.into_iter.IntoIter A) (core.slice.iter.Iter B)) (A × B) where
  next := core.iter.adapters.zip.VecSliceZip.next
  fold := core.iter.adapters.zip.VecSliceZip.fold
  step_by := core.iter.traits.iterator.Iterator.step_by.default
  enumerate := core.iter.traits.iterator.Iterator.enumerate.default
  take := core.iter.traits.iterator.Iterator.take.default

end Aeneas.Std
