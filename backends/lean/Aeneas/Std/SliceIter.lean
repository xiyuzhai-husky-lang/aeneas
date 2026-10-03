/- Arrays/Slices -/
module
public import Aeneas.Std.Slice
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Core.Iter
public meta import Aeneas.Std.Core.Iter
meta import Aeneas.Std.Slice
meta import Aeneas.Std.Array.Array
public section

@[expose] section

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD


@[rust_type "core::slice::iter::Iter"]
structure core.slice.iter.Iter (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_type "core::slice::iter::IterMut" (mutRegions := #[0]) (body := .opaque)]
structure core.slice.iter.IterMut (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat := 0

@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[rust_fun "core::slice::{[@T]}::contains"]
def core.slice.Slice.contains {T : Type} (partialEqInst : core.cmp.PartialEq T T)
  (s : Slice T) (x : T) : Result Bool :=
  List.anyM (partialEqInst.eq x) s.val

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, @T>, &'a mut @T>}::next"]
def core.slice.iter.IteratorIterMut.next
  {T : Type}
  (it : core.slice.iter.IterMut T) :
  Result ((Option T) × (core.slice.iter.IterMut T) ×
          (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T)) :=
  if h: it.i < it.slice.len then
    let x := it.slice[it.i]
    let i := it.i
    let it := { it with i := i + 1 }
    let back it' x :=
      match x with
      | none => it'
      | some x => { it' with slice := it'.slice.setAtNat i x }
    ok (some x, it, back)
  else ok (none, it, fun it _ => it)

@[rust_fun "core::slice::{[@T]}::iter_mut"]
def core.slice.Slice.iter_mut {T : Type} (slice : Slice T) :
  Result ((core.slice.iter.IterMut T) × (core.slice.iter.IterMut T → Slice T)) :=
  ok ({slice}, fun it => it.slice)

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next"]
def core.slice.iter.IteratorSliceIter.next
  {T : Type} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.len then
    let x := it.slice[it.i]
    let it := { it with i := it.i + 1}
    ok (some x, it)
  else ok (none, it)

/- Prototype functional models. The native slice iterator uses unsafe pointers;
   correspondence to those bodies is NOT proved here. These definitions specify
   exactly the remaining window, callback order, and modeled failures/divergence. -/
def core.slice.iter.Iter.remaining {T : Type} (it : core.slice.iter.Iter T) : List T :=
  it.slice.val.drop it.i

@[rust_fun "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold"]
def core.slice.iter.IteratorSliceIter.fold {T B F : Type}
    (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) : Result B := do
  let (result, _) ← it.remaining.foldlM
    (fun (state : B × F) item => fn.call_mut state.2 (state.1, item)) (init, f)
  ok result

@[rust_fun "core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next_back"]
def core.slice.iter.DoubleEndedIteratorSliceIter.next_back {T : Type}
    (it : core.slice.iter.Iter T) : Result (Option T × core.slice.iter.Iter T) :=
  if h : it.i < it.slice.val.length then
    let last := it.slice.val[it.slice.val.length - 1]'(by omega)
    let shortened :=  Slice.from (it.slice.val.take (it.slice.val.length - 1))
      (by have := it.slice.property; simp only [List.length_take]; omega)
    ok (some last, { it with slice := shortened })
  else ok (none, it)

@[rust_fun "core::slice::iter::{core::iter::traits::exact_size::ExactSizeIterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::len"]
def core.slice.iter.ExactSizeIteratorSliceIter.len {T : Type}
    (it : core.slice.iter.Iter T) : Result Usize :=
  ok (Usize.ofNatCore it.remaining.length
    (by have := it.slice.property; simp only [core.slice.iter.Iter.remaining, List.length_drop]; scalar_tac))

namespace IteratorPrototype

theorem remaining_length {T : Type} (it : core.slice.iter.Iter T) :
    it.remaining.length = it.slice.val.length - it.i := by
  simp [core.slice.iter.Iter.remaining]

theorem slice_len_contents {T : Type} (it : core.slice.iter.Iter T) :
    ∃ n, core.slice.iter.ExactSizeIteratorSliceIter.len it = ok n ∧
      n.val = it.remaining.length := by
  exact ⟨_, rfl, rfl⟩

theorem slice_next_back_contents {T : Type} (it : core.slice.iter.Iter T) :
    ∃ item it', core.slice.iter.DoubleEndedIteratorSliceIter.next_back it = ok (item, it') ∧
      item = it.remaining.getLast? ∧ it'.remaining = it.remaining.dropLast := by
  unfold core.slice.iter.DoubleEndedIteratorSliceIter.next_back
  split
  next h =>
    refine ⟨_, _, rfl, ?_, ?_⟩
    · simp only [core.slice.iter.Iter.remaining, List.getLast?_drop, if_neg (by omega : ¬ it.slice.val.length ≤ it.i)]
      rw [List.getLast?_eq_getElem?]
      simp only [List.getElem?_eq_getElem (by omega : it.slice.val.length - 1 < it.slice.val.length)]
    · simp only [core.slice.iter.Iter.remaining, Slice.from_val, List.dropLast_eq_take,
        List.length_drop, List.drop_take]
      congr 1
      omega
  next h =>
    refine ⟨_, _, rfl, ?_, ?_⟩ <;>
      simp [core.slice.iter.Iter.remaining, List.drop_eq_nil_of_le (by omega : it.slice.val.length ≤ it.i)]

theorem slice_next_back_preserves_valid {T : Type} (it : core.slice.iter.Iter T)
    (valid : it.i ≤ it.slice.val.length) {item it'}
    (step : core.slice.iter.DoubleEndedIteratorSliceIter.next_back it = ok (item, it')) :
    it'.i ≤ it'.slice.val.length := by
  unfold core.slice.iter.DoubleEndedIteratorSliceIter.next_back at step
  split at step
  next h =>
    have hs := Result.ok_injective step
    cases hs
    simp only [Slice.from_val, List.length_take]
    omega
  next h =>
    have hs := Result.ok_injective step
    cases hs
    exact valid

theorem slice_fold_contents {T B F : Type} (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) :
    core.slice.iter.IteratorSliceIter.fold fn it init f = (do
      let state ← it.remaining.foldlM
        (fun (state : B × F) item => fn.call_mut state.2 (state.1, item)) (init, f)
      ok state.1) := rfl

end IteratorPrototype

namespace IteratorPrototype

theorem slice_fold_empty {T B F : Type} (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) (h : it.remaining = []) :
    core.slice.iter.IteratorSliceIter.fold fn it init f = ok init := by
  simp [core.slice.iter.IteratorSliceIter.fold, h]

theorem slice_fold_cons {T B F : Type} (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) (item : T) (rest : List T)
    (h : it.remaining = item :: rest) :
    core.slice.iter.IteratorSliceIter.fold fn it init f = (do
      let state ← fn.call_mut f (init, item)
      let out ← rest.foldlM
        (fun (state : B × F) item => fn.call_mut state.2 (state.1, item)) state
      ok out.1) := by
  simp only [core.slice.iter.IteratorSliceIter.fold, h, List.foldlM_cons, bind_assoc]

theorem slice_fold_callback_fail {T B F : Type} (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) (item : T) (rest : List T)
    (e : Error) (h : it.remaining = item :: rest)
    (hf : fn.call_mut f (init, item) = fail e) :
    core.slice.iter.IteratorSliceIter.fold fn it init f = fail e := by
  rw [slice_fold_cons fn it init f item rest h]
  simp only [hf, bind_tc_fail]

theorem slice_fold_callback_div {T B F : Type} (fn : core.ops.function.FnMut F (B × T) B)
    (it : core.slice.iter.Iter T) (init : B) (f : F) (item : T) (rest : List T)
    (h : it.remaining = item :: rest) (hf : fn.call_mut f (init, item) = .div) :
    core.slice.iter.IteratorSliceIter.fold fn it init f = .div := by
  rw [slice_fold_cons fn it init f item rest h]
  simp only [hf, bind_tc_div]

end IteratorPrototype

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>"]
impl_def core.iter.traits.iterator.IteratorSliceIter (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.Iter T) T := {
  next := core.slice.iter.IteratorSliceIter.next
  fold := core.slice.iter.IteratorSliceIter.fold
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.iter.traits.iterator.IteratorSliceIter T)
}

-- ============================================================================
-- IntoIterator for shared array references: &[T; N] → Iter<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&[T; N]`.
Mirrors Rust: `(&[T; N]).into_iter()` returns an `Iter<T>` over the array
viewed as a slice. -/
@[rust_fun
  "core::array::{core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    {T : Type} {N : Usize} (a : Array T N) : Result (core.slice.iter.Iter T) :=
  ok ⟨ .from a.val (by scalar_tac), 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T; @N], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type) (N : Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

-- ============================================================================
-- IntoIterator for shared slice references: &[T] → Iter<T>
-- ============================================================================

/-- Model for `IntoIterator::into_iter` for `&[T]`.
Mirrors Rust: `(&[T]).into_iter()` returns an `Iter<T>` starting at index 0. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[reducible, rust_trait_impl
  "core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>"]
def SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
    (T : Type) :
    core.iter.traits.collect.IntoIterator (Slice T) T (core.slice.iter.Iter T) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceIter T
  into_iter := SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
}

@[rust_type "core::slice::iter::ChunksExact" (body := .opaque)]
structure core.slice.iter.ChunksExact (T : Type) where
  chunks : List (Slice T)
  remainder : Slice T

@[rust_fun
  "core::slice::iter::{core::slice::iter::ChunksExact<'a, @T>}::remainder"]
def core.slice.iter.ChunksExact.getRemainder
  {T : Type} (self : core.slice.iter.ChunksExact T) : Result (Slice T) :=
  ok self.remainder

@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>}::next"]
def core.slice.iter.IteratorChunksExact.next
  {T : Type} (self : core.slice.iter.ChunksExact T) :
  Result ((Option (Slice T)) × (core.slice.iter.ChunksExact T)) :=
  match self.chunks with
  | [] => ok (none, self)
  | chunk :: chunks => ok (some chunk, { chunks, remainder := self.remainder })

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExact<'a, @T>, &'a [@T]>"]
impl_def core.iter.traits.iterator.IteratorChunksExact (T : Type) :
  core.iter.traits.iterator.Iterator (core.slice.iter.ChunksExact T) (Slice T)
  := {
  next := core.slice.iter.IteratorChunksExact.next
  fold := core.iter.traits.iterator.Iterator.fold.default core.slice.iter.IteratorChunksExact.next
  step_by := core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
  enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
  take := core.iter.traits.iterator.Iterator.take.trait_default
    (core.iter.traits.iterator.IteratorChunksExact T)
}

/-- Split a list into non-overlapping chunks of exactly size `n`, returning the
    full-sized chunks and the trailing remainder (which has fewer than `n` elements). -/
def List.toChunksExact (n : Nat) (hn : 0 < n) (l : List α) :
    List (List α) × List α :=
  if _h : l.length < n then ([], l)
  else
    let (chunks, rem) := toChunksExact n hn (l.drop n)
    (l.take n :: chunks, rem)
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem List.toChunksExact_chunk_length
    {n : Nat} (hn : 0 < n) (l : List α) :
    ∀ c ∈ (List.toChunksExact n hn l).1, c.length ≤ n := by
  unfold toChunksExact
  split
  · simp
  · simp only [List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simp [List.length_take]
    · exact toChunksExact_chunk_length hn _ c hc
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem List.toChunksExact_remainder_length
    {n : Nat} (hn : 0 < n) (l : List α) :
    (List.toChunksExact n hn l).2.length ≤ l.length := by
  unfold toChunksExact
  split
  · simp
  · simp only []
    have := toChunksExact_remainder_length hn (l.drop n)
    simp [List.length_drop] at this
    omega
termination_by l.length
decreasing_by simp [List.length_drop]; omega

@[rust_fun "core::slice::{[@T]}::chunks_exact"]
def core.slice.Slice.chunks_exact {T : Type} (s : Slice T) (chunk_size : Std.Usize) :
  Result (core.slice.iter.ChunksExact T) :=
  if hcs : chunk_size.val > 0 then
    let result := List.toChunksExact chunk_size.val hcs s.val
    let sliceChunks := result.1.attach.map fun ⟨c, hc⟩ => .from c (by
        have := List.toChunksExact_chunk_length hcs s.val c hc
        scalar_tac)
    ok { chunks := sliceChunks,
         remainder := .from result.2 (by
           have := List.toChunksExact_remainder_length hcs s.val
           grind) }
  else fail .panic


-- ============================================================================
-- StepBy tests
-- ============================================================================

private def mkSliceIter (l : List Nat) (h : l.length ≤ Usize.max := by scalar_tac) :
    core.slice.iter.Iter Nat :=
  { slice := .from l h, i := 0 }

private def collectStepBy (sbi : core.iter.adapters.step_by.StepBy (core.slice.iter.Iter Nat))
    (fuel : Nat := 100) : Result (List Nat) :=
  match fuel with
  | 0 => .ok []
  | fuel + 1 => do
    let (opt, sbi) ←
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorSliceIter Nat) sbi
    match opt with
    | none => .ok []
    | some x => do
      let rest ← collectStepBy sbi fuel
      .ok (x :: rest)

-- step_by(0) panics
#assert
  match (core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1, 2, 3]) 0#usize).match with
  | .vis (.fail e) _ => e == panic
  | _ => false

-- step_by(1) returns all elements
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4]) 1#usize
  collectStepBy sbi).reducesTo [0, 1, 2, 3, 4]

-- step_by(2) returns every other element
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4]) 2#usize
  collectStepBy sbi).reducesTo [0, 2, 4]

-- step_by(3)
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2, 3, 4, 5, 6]) 3#usize
  collectStepBy sbi).reducesTo [0, 3, 6]

-- step_by larger than collection: returns only first element
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 10#usize
  collectStepBy sbi).reducesTo [0]

-- step_by on empty iterator
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter []) 2#usize
  collectStepBy sbi).reducesTo []

-- step_by(1) on single element
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [42]) 1#usize
  collectStepBy sbi).reducesTo [42]

-- step_by(2) on single element
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [42]) 2#usize
  collectStepBy sbi).reducesTo [42]

-- step_by equal to length: returns only first element
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 3#usize
  collectStepBy sbi).reducesTo [0]

-- step_by = length - 1
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi).reducesTo [0, 2]

-- step_by(2) on two elements: returns only first
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1]) 2#usize
  collectStepBy sbi).reducesTo [0]

-- step_by(2) on three elements: returns first and third
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [0, 1, 2]) 2#usize
  collectStepBy sbi).reducesTo [0, 2]

-- step_by(4) on longer sequence
#assert (do
  let sbi ← core.iter.traits.iterator.Iterator.step_by.default
    (mkSliceIter [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) 4#usize
  collectStepBy sbi).reducesTo [0, 4, 8]

-- Verify that step_by(0) on the generic Iterator.step_by.default also panics
#assert
  match (core.iter.traits.iterator.Iterator.step_by.default (mkSliceIter [1]) 0#usize).match with
  | .vis (.fail e) _ => e == panic
  | _ => false

-- Nested StepBy dictionary test omitted: its Iterator binding is unsupported in this prototype.

-- ============================================================================
-- Step specs for SharedArray.into_iter and SharedSlice.into_iter
-- ============================================================================

@[step]
theorem SharedArray.into_iter.spec {T : Type} {N : Usize} (a : Array T N) :
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter a
    ⦃ (iter : core.slice.iter.Iter T) =>
      iter.slice.val = a.val ∧ iter.i = 0 ⦄ := by
  simp [SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]

@[step]
theorem SharedSlice.into_iter.spec {T : Type} (s : Slice T) :
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    ⦃ (iter : core.slice.iter.Iter T) =>
      iter.slice = s ∧ iter.i = 0 ⦄ := by
  simp [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, WP.spec_ok]
end Aeneas.Std
