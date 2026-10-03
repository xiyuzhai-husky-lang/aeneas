module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public section

@[expose] section

open Aeneas Aeneas.Std Result

namespace SliceZipPrototype

-- Deliberately unregistered. These are logical model laws, not a proof of the
-- unsafe native slice/Zip representation or native specialization selection.
def window {A B : Type} (left : core.slice.iter.Iter A)
    (right : core.slice.iter.Iter B) : List (A × B) :=
  left.remaining.zip right.remaining

-- Keep the closure state in the fold accumulator, exactly as FnMut requires.
def foldWindow {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (items : List Item) (acc : Acc) (f : F) : Result Acc := do
  let state ← items.foldlM (m := Result)
    (fun (state : Acc × F) item => fn.call_mut state.2 (state.1, item)) (acc, f)
  ok state.1

def fold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : core.slice.iter.Iter B)
    (acc : Acc) (f : F) : Result Acc :=
  foldWindow fn (window left right) acc f

theorem window_length {A B : Type} (left : core.slice.iter.Iter A)
    (right : core.slice.iter.Iter B) :
    (window left right).length = min (left.slice.val.length - left.i)
      (right.slice.val.length - right.i) := by
  simp [window, core.slice.iter.Iter.remaining]

theorem window_pair_at {A B : Type} (left : core.slice.iter.Iter A)
    (right : core.slice.iter.Iter B) (i : Nat) :
    (window left right)[i]? =
      left.slice.val[left.i + i]?.bind (fun a =>
        right.slice.val[right.i + i]?.map (fun b => (a, b))) := by
  simp [window, core.slice.iter.Iter.remaining, List.zip, List.getElem?_zipWith', Option.bind_map]

theorem foldWindow_nil {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc) (acc : Acc) (f : F) :
    foldWindow fn [] acc f = ok acc := by
  simp only [foldWindow, List.foldlM_nil, pure_tc_eq, bind_tc_ok]

theorem foldWindow_cons {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (item : Item) (rest : List Item) (acc : Acc) (f : F) :
    foldWindow fn (item :: rest) acc f = (do
      let (acc', f') ← fn.call_mut f (acc, item)
      foldWindow fn rest acc' f') := by
  simp only [foldWindow, List.foldlM_cons]
  simp only [bind_tc_eq, Aeneas.Std.bind_assoc]

theorem foldWindow_callback_fail {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (item : Item) (rest : List Item) (acc : Acc) (f : F) (error : Error)
    (h : fn.call_mut f (acc, item) = fail error) :
    foldWindow fn (item :: rest) acc f = fail error := by
  rw [foldWindow_cons, h]
  simp

theorem foldWindow_callback_div {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (item : Item) (rest : List Item) (acc : Acc) (f : F)
    (h : fn.call_mut f (acc, item) = .div) :
    foldWindow fn (item :: rest) acc f = .div := by
  rw [foldWindow_cons, h]
  simp

theorem foldWindow_callback_state {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (item : Item) (rest : List Item) (acc acc' : Acc) (f f' : F)
    (h : fn.call_mut f (acc, item) = ok (acc', f')) :
    foldWindow fn (item :: rest) acc f = foldWindow fn rest acc' f' := by
  rw [foldWindow_cons, h]
  simp

-- This relation includes the entire finite produced sequence. No callback
-- assumptions, success-only premise, or artificial fuel bound are present.
inductive Produces {I Item : Type} (next : I → Result (Option Item × I)) :
    I → List Item → Prop
  | nil (iter rest : I) (h : next iter = ok (none, rest)) : Produces next iter []
  | cons (iter rest : I) (item : Item) (tail : List Item)
      (h : next iter = ok (some item, rest))
      (later : Produces next rest tail) : Produces next iter (item :: tail)

theorem defaultFold_of_produces {I Item Acc F : Type}
    (next : I → Result (Option Item × I))
    (fn : core.ops.function.FnMut F (Acc × Item) Acc)
    (iter : I) (items : List Item) (produces : Produces next iter items)
    (acc : Acc) (f : F) :
    core.iter.traits.iterator.Iterator.fold.default next fn iter acc f =
      foldWindow fn items acc f := by
  induction produces generalizing acc f with
  | nil iter rest h =>
    rw [core.iter.traits.iterator.Iterator.fold.default_none next fn iter rest acc f h]
    simp [foldWindow_nil]
  | cons iter rest item tail h later ih =>
    rw [core.iter.traits.iterator.Iterator.fold.default, foldWindow_cons]
    simp only [h, bind_tc_ok]
    congr 1
    funext state
    exact ih state.1 state.2


def next {A B : Type}
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) :=
  core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
    (core.iter.traits.iterator.IteratorSliceIter A)
    (core.iter.traits.iterator.IteratorSliceIter B) z

theorem sliceZip_produces {A B : Type}
    (left : core.slice.iter.Iter A) (right : core.slice.iter.Iter B) :
    Produces next ⟨left, right⟩ (window left right) := by
  by_cases hl : left.i < left.slice.val.length
  · by_cases hr : right.i < right.slice.val.length
    · have hw : window left right = (left.slice.val[left.i], right.slice.val[right.i]) ::
          window {left with i := left.i + 1} {right with i := right.i + 1} := by
        simp only [window, core.slice.iter.Iter.remaining]
        rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hr]
        rfl
      rw [hw]
      apply Produces.cons _ ⟨{left with i := left.i + 1}, {right with i := right.i + 1}⟩
      · simp [next, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
          core.slice.iter.IteratorSliceIter.next,
          hl, hr]
        constructor <;> rfl
      · exact sliceZip_produces _ _
    · have hw : window left right = [] := by
        simp [window, core.slice.iter.Iter.remaining, List.drop_eq_nil_of_le (by omega :
          right.slice.val.length ≤ right.i)]
      rw [hw]
      apply Produces.nil _ ⟨{left with i := left.i + 1}, right⟩
      simp [next, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
        core.slice.iter.IteratorSliceIter.next,
        hl, hr]
  · have hw : window left right = [] := by
      simp [window, core.slice.iter.Iter.remaining, List.drop_eq_nil_of_le (by omega :
        left.slice.val.length ≤ left.i)]
    rw [hw]
    apply Produces.nil _ ⟨left, right⟩
    simp [next, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
      core.slice.iter.IteratorSliceIter.next,
      hl]
termination_by left.slice.val.length - left.i

theorem fold_eq_modeled_next {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (left : core.slice.iter.Iter A) (right : core.slice.iter.Iter B)
    (acc : Acc) (f : F) :
    core.iter.traits.iterator.Iterator.fold.default next fn ⟨left, right⟩ acc f =
      fold fn left right acc f := by
  exact defaultFold_of_produces next fn _ _ (sliceZip_produces left right) acc f

end SliceZipPrototype


namespace Aeneas.Std

/-- Applied external-library model. The compiler must establish the exact
shared slice constructors/witnesses. Native unsafe specialization correspondence
is an explicit library boundary; the logical laws above do not prove it. -/
def core.iter.adapters.zip.SliceZip.next {A B : Type}
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) :=
  SliceZipPrototype.next z

def core.iter.adapters.zip.SliceZip.fold {A B Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (A × B)) Acc)
    (z : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B))
    (acc : Acc) (f : F) : Result Acc :=
  SliceZipPrototype.fold fn z.fst z.snd acc f

/-- All retained Iterator fields are provided explicitly. This is deliberately
not registered as a declaration-wide model for arbitrary Zip<A, B>. -/
def core.iter.traits.iterator.IteratorSliceZip (A B : Type) :
    core.iter.traits.iterator.Iterator
      (core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) (A × B) where
  next := core.iter.adapters.zip.SliceZip.next
  fold := core.iter.adapters.zip.SliceZip.fold
  step_by := core.iter.traits.iterator.Iterator.step_by.default
  enumerate := core.iter.traits.iterator.Iterator.enumerate.default
  take := core.iter.traits.iterator.Iterator.take.default

end Aeneas.Std
