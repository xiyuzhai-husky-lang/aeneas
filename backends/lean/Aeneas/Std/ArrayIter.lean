module
public import Aeneas.Std.Array.Array
public import Aeneas.Std.VecIter
@[expose] public section

namespace Aeneas.Std
open Result

/-- Owned, unconsumed array elements in forward order. The native iterator's
unsafe storage, deallocation and Drop behavior remain library-model boundaries. -/
@[rust_type "core::array::iter::IntoIter" (body := .opaque)]
structure core.array.iter.IntoIter (T : Type) (N : Usize) where
  remaining : List T
  bounded : remaining.length ≤ N.val

@[rust_fun "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IteratorIntoIter.next {T : Type} {N : Usize}
    (it : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  match h : it.remaining with
  | [] => ok (none, it)
  | item :: rest => ok (some item, ⟨rest, by have := it.bounded; simp only [h, List.length_cons] at this; omega⟩)

/-- The native array override folds its remaining initialized window, carrying
both the accumulator and each returned FnMut state. -/
@[rust_fun "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::fold"]
def core.array.iter.IteratorIntoIter.fold {T B F : Type} {N : Usize}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.array.iter.IntoIter T N) (acc : B) (f : F) : Result B :=
  alloc.vec.into_iter.IteratorIntoIter.foldList fn it.remaining acc f

@[reducible, rust_trait_impl "core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>"]
def core.iter.traits.iterator.IteratorArrayIntoIter (T : Type) (N : Usize) :
    core.iter.traits.iterator.Iterator (core.array.iter.IntoIter T N) T where
  next := core.array.iter.IteratorIntoIter.next
  fold := core.array.iter.IteratorIntoIter.fold

@[rust_fun "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def core.array.IntoIteratorArray.into_iter {T : Type} {N : Usize}
    (array : Array T N) : Result (core.array.iter.IntoIter T N) :=
  ok ⟨array.val, by simp⟩

@[reducible, rust_trait_impl "core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>"]
def core.iter.traits.collect.IntoIteratorArray (T : Type) (N : Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T (core.array.iter.IntoIter T N) where
  iteratorInst := core.iter.traits.iterator.IteratorArrayIntoIter T N
  into_iter := core.array.IntoIteratorArray.into_iter

namespace ArrayIterator

theorem next_empty {T : Type} {N : Usize} (it : core.array.iter.IntoIter T N)
    (h : it.remaining = []) :
    core.array.iter.IteratorIntoIter.next it = ok (none, it) := by
  rcases it with ⟨items, bound⟩
  dsimp at h
  subst items
  simp [core.array.iter.IteratorIntoIter.next]

theorem next_cons {T : Type} {N : Usize} (it : core.array.iter.IntoIter T N)
    (item : T) (tail : List T) (h : it.remaining = item :: tail) :
    ∃ rest, core.array.iter.IteratorIntoIter.next it = ok (some item, rest) ∧
      rest.remaining = tail := by
  rcases it with ⟨items, bound⟩
  dsimp at h
  subst items
  simp [core.array.iter.IteratorIntoIter.next]

theorem into_iter_contents {T : Type} {N : Usize} (array : Array T N) :
    ∃ it, core.array.IntoIteratorArray.into_iter array = ok it ∧
      it.remaining = array.val := by
  simp [core.array.IntoIteratorArray.into_iter]

theorem fold_exact {T B F : Type} {N : Usize}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.array.iter.IntoIter T N) (acc : B) (f : F) :
    core.array.iter.IteratorIntoIter.fold fn it acc f = (do
      let state ← it.remaining.foldlM
        (fun state item => fn.call_mut state.2 (state.1, item)) (acc, f)
      ok state.1) :=
  alloc.vec.into_iter.IteratorIntoIter.foldList_eq_foldlM fn it.remaining acc f

end ArrayIterator
end Aeneas.Std
