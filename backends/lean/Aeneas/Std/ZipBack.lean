module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public import Aeneas.Std.SliceZip
public section
@[expose] section
namespace Aeneas.Std
open Result

namespace ZipBack
/-- Discard exactly the requested number of reverse calls, including calls
returning `None`. Every returned iterator state and outer error is retained. -/
def discard {I Item : Type} (next : I → Result (Option Item × I)) :
    Nat → I → Result I
  | 0, iter => ok iter
  | n + 1, iter => do
    let (_, iter) ← next iter
    discard next n iter

/-- Both final calls occur, in left-to-right order, even if the first is `None`.
A mismatched pair panics exactly as the native unreachable branch does. -/
def pair {A B X Y : Type}
    (left : A → Result (Option X × A)) (right : B → Result (Option Y × B))
    (self : core.iter.adapters.zip.Zip A B) :
    Result (Option (X × Y) × core.iter.adapters.zip.Zip A B) := do
  let (x, a) ← left self.fst
  let (y, b) ← right self.snd
  match x, y with
  | some x, some y => ok (some (x, y), ⟨a, b⟩)
  | none, none => ok (none, ⟨a, b⟩)
  | _, _ => fail .panic
end ZipBack

/-- The ordinary Zip reverse algorithm first measures both iterators, discards
only the longer tail, then reads one item from each side. This library model
uses the existing two-iterator abstraction of Zip; it makes no trait-law
assumption and preserves the native inconsistent-length panic. -/
@[rust_fun
  "core::iter::adapters::zip::{core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::zip::Zip<@A, @B>, (@Clause0_Clause0_Item, @Clause2_Clause0_Item)>}::next_back"]
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back
    {A B X Y : Type}
    (left : core.iter.traits.double_ended.DoubleEndedIterator A X)
    (leftSize : core.iter.traits.exact_size.ExactSizeIterator A X)
    (right : core.iter.traits.double_ended.DoubleEndedIterator B Y)
    (rightSize : core.iter.traits.exact_size.ExactSizeIterator B Y)
    (self : core.iter.adapters.zip.Zip A B) :
    Result (Option (X × Y) × core.iter.adapters.zip.Zip A B) := do
  let aSize ← leftSize.len self.fst
  let bSize ← rightSize.len self.snd
  let self ←
    if aSize.val > bSize.val then do
      let a ← ZipBack.discard left.next_back (aSize.val - bSize.val) self.fst
      ok {self with fst := a}
    else do
      let b ← ZipBack.discard right.next_back (bSize.val - aSize.val) self.snd
      ok {self with snd := b}
  ZipBack.pair left.next_back right.next_back self

namespace ZipBack
variable {I Item A B X Y : Type}

theorem discard_zero (next : I → Result (Option Item × I)) (iter : I) :
    discard next 0 iter = ok iter := rfl

theorem discard_step (next : I → Result (Option Item × I))
    (n : Nat) (iter after : I) (item : Option Item)
    (step : next iter = ok (item, after)) :
    discard next (n + 1) iter = discard next n after := by
  simp [discard, step]

theorem discard_fail (next : I → Result (Option Item × I))
    (n : Nat) (iter : I) (error : Error) (step : next iter = fail error) :
    discard next (n + 1) iter = fail error := by simp [discard, step]

theorem discard_div (next : I → Result (Option Item × I))
    (n : Nat) (iter : I) (step : next iter = div) :
    discard next (n + 1) iter = div := by simp [discard, step]

theorem pair_some (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (b : B) (x : X) (y : Y)
    (ha : left self.fst = ok (some x, a)) (hb : right self.snd = ok (some y, b)) :
    pair left right self = ok (some (x, y), ⟨a, b⟩) := by simp [pair, ha, hb]

theorem pair_none (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (b : B)
    (ha : left self.fst = ok (none, a)) (hb : right self.snd = ok (none, b)) :
    pair left right self = ok (none, ⟨a, b⟩) := by simp [pair, ha, hb]

theorem pair_left_only (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (b : B) (x : X)
    (ha : left self.fst = ok (some x, a)) (hb : right self.snd = ok (none, b)) :
    pair left right self = fail .panic := by simp [pair, ha, hb]

theorem pair_right_only (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (b : B) (y : Y)
    (ha : left self.fst = ok (none, a)) (hb : right self.snd = ok (some y, b)) :
    pair left right self = fail .panic := by simp [pair, ha, hb]

theorem pair_right_failure (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (x : Option X) (error : Error)
    (ha : left self.fst = ok (x, a)) (hb : right self.snd = fail error) :
    pair left right self = fail error := by simp [pair, ha, hb]

theorem pair_right_div (left : A → Result (Option X × A))
    (right : B → Result (Option Y × B)) (self : core.iter.adapters.zip.Zip A B)
    (a : A) (x : Option X)
    (ha : left self.fst = ok (x, a)) (hb : right self.snd = div) :
    pair left right self = div := by simp [pair, ha, hb]

abbrev nativeNext := @core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back

theorem next_equal
    (left : core.iter.traits.double_ended.DoubleEndedIterator A X)
    (leftSize : core.iter.traits.exact_size.ExactSizeIterator A X)
    (right : core.iter.traits.double_ended.DoubleEndedIterator B Y)
    (rightSize : core.iter.traits.exact_size.ExactSizeIterator B Y)
    (self : core.iter.adapters.zip.Zip A B) (size : Usize)
    (ha : leftSize.len self.fst = ok size) (hb : rightSize.len self.snd = ok size) :
    nativeNext left leftSize right rightSize self = pair left.next_back right.next_back self := by
  simp [nativeNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back,
    ha, hb, discard]

theorem next_left_longer
    (left : core.iter.traits.double_ended.DoubleEndedIterator A X)
    (leftSize : core.iter.traits.exact_size.ExactSizeIterator A X)
    (right : core.iter.traits.double_ended.DoubleEndedIterator B Y)
    (rightSize : core.iter.traits.exact_size.ExactSizeIterator B Y)
    (self : core.iter.adapters.zip.Zip A B) (aSize bSize : Usize)
    (ha : leftSize.len self.fst = ok aSize) (hb : rightSize.len self.snd = ok bSize)
    (longer : bSize.val < aSize.val) :
    nativeNext left leftSize right rightSize self = (do
      let a ← discard left.next_back (aSize.val - bSize.val) self.fst
      pair left.next_back right.next_back {self with fst := a}) := by
  simp [nativeNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back,
    ha, hb, longer]

theorem next_right_longer
    (left : core.iter.traits.double_ended.DoubleEndedIterator A X)
    (leftSize : core.iter.traits.exact_size.ExactSizeIterator A X)
    (right : core.iter.traits.double_ended.DoubleEndedIterator B Y)
    (rightSize : core.iter.traits.exact_size.ExactSizeIterator B Y)
    (self : core.iter.adapters.zip.Zip A B) (aSize bSize : Usize)
    (ha : leftSize.len self.fst = ok aSize) (hb : rightSize.len self.snd = ok bSize)
    (longer : aSize.val < bSize.val) :
    nativeNext left leftSize right rightSize self = (do
      let b ← discard right.next_back (bSize.val - aSize.val) self.snd
      pair left.next_back right.next_back {self with snd := b}) := by
  simp [nativeNext, core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back, ha, hb]
  intro impossible
  omega


theorem discard_slice_contents {T : Type} (n : Nat) (iter : core.slice.iter.Iter T) :
    ∃ after, discard core.slice.iter.DoubleEndedIteratorSliceIter.next_back n iter = ok after ∧
      after.remaining = iter.remaining.take (iter.remaining.length - n) := by
  induction n generalizing iter with
  | zero => exact ⟨iter, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨item, next, step, _, contents⟩ := IteratorPrototype.slice_next_back_contents iter
    obtain ⟨after, run, rest⟩ := ih next
    refine ⟨after, ?_, ?_⟩
    · simp [discard, step, run]
    · rw [rest, contents]
      simp only [List.dropLast_eq_take, List.length_take, List.take_take]
      congr 1
      omega


theorem pair_slice_contents {T U : Type} (left : core.slice.iter.Iter T)
    (right : core.slice.iter.Iter U) (same : left.remaining.length = right.remaining.length) :
    ∃ item a b, pair core.slice.iter.DoubleEndedIteratorSliceIter.next_back
        core.slice.iter.DoubleEndedIteratorSliceIter.next_back ⟨left, right⟩ = ok (item, ⟨a,b⟩) ∧
      item = (left.remaining.zip right.remaining).getLast? ∧
      a.remaining = left.remaining.dropLast ∧ b.remaining = right.remaining.dropLast := by
  obtain ⟨x, a, ha, hx, ar⟩ := IteratorPrototype.slice_next_back_contents left
  obtain ⟨y, b, hb, hy, br⟩ := IteratorPrototype.slice_next_back_contents right
  cases x with
  | none =>
    have leftNil : left.remaining = [] := List.getLast?_eq_none_iff.mp hx.symm
    have rightNil : right.remaining = [] := List.eq_nil_of_length_eq_zero (by simpa [leftNil] using same.symm)
    have yNil : y = none := by simpa [rightNil] using hy
    rw [yNil] at hb
    exact ⟨none, a, b, pair_none _ _ _ _ _ ha hb, by simp [leftNil], ar, br⟩
  | some x =>
    obtain ⟨xs, leftShape⟩ := List.getLast?_eq_some_iff.mp hx.symm
    cases y with
    | none =>
      have rightNil : right.remaining = [] := List.getLast?_eq_none_iff.mp hy.symm
      simp [leftShape, rightNil] at same
    | some y =>
      obtain ⟨ys, rightShape⟩ := List.getLast?_eq_some_iff.mp hy.symm
      have lengths : xs.length = ys.length := by simpa [leftShape, rightShape] using same
      refine ⟨some (x,y), a, b, pair_some _ _ _ _ _ _ _ ha hb, ?_, ar, br⟩
      simp [leftShape, rightShape, List.zip_append lengths]

def sliceNext {T U : Type} (self : core.iter.adapters.zip.Zip
    (core.slice.iter.Iter T) (core.slice.iter.Iter U)) :=
  nativeNext (core.iter.traits.double_ended.DoubleEndedIteratorSliceIter T)
    (core.iter.traits.exact_size.ExactSizeIteratorSliceIter T)
    (core.iter.traits.double_ended.DoubleEndedIteratorSliceIter U)
    (core.iter.traits.exact_size.ExactSizeIteratorSliceIter U) self

theorem slice_next_equal_contents {T U : Type} (left : core.slice.iter.Iter T)
    (right : core.slice.iter.Iter U) (same : left.remaining.length = right.remaining.length) :
    ∃ item a b, sliceNext ⟨left, right⟩ = ok (item, ⟨a,b⟩) ∧
      item = (left.remaining.zip right.remaining).getLast? ∧
      a.remaining = left.remaining.dropLast ∧ b.remaining = right.remaining.dropLast := by
  obtain ⟨aSize, ha, va⟩ := IteratorPrototype.slice_len_contents left
  obtain ⟨bSize, hb, vb⟩ := IteratorPrototype.slice_len_contents right
  have eqSize : aSize = bSize := by apply UScalar.eq_of_val_eq; omega
  subst bSize
  obtain ⟨item, a, b, run, last, ar, br⟩ := pair_slice_contents left right same
  refine ⟨item, a, b, ?_, last, ar, br⟩
  change nativeNext _ _ _ _ _ = _
  rw [next_equal _ _ _ _ _ aSize ha hb]
  exact run

end ZipBack
end Aeneas.Std

namespace Aeneas.Std
open Result
@[expose] section

/-- Zip does not override rfold: it is the native repeated next_back loop,
including callback state, iterator errors and divergence. -/
def core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.rfold
    {A B X Y Acc F : Type}
    (left : core.iter.traits.double_ended.DoubleEndedIterator A X)
    (leftSize : core.iter.traits.exact_size.ExactSizeIterator A X)
    (right : core.iter.traits.double_ended.DoubleEndedIterator B Y)
    (rightSize : core.iter.traits.exact_size.ExactSizeIterator B Y)
    (fn : core.ops.function.FnMut F (Acc × (X × Y)) Acc)
    (self : core.iter.adapters.zip.Zip A B) (init : Acc) (closure : F) : Result Acc :=
  core.iter.traits.iterator.Iterator.fold.default
    (Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.next_back left leftSize right rightSize)
    fn self init closure

/-- Exact shared-slice instance; no claim about arbitrary foreign iterator
size_hint implementations or unsafe Zip representation is needed. -/
def core.iter.adapters.zip.SliceZip.len {A B : Type}
    (self : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) :
    Result Usize := do
  let a ← core.slice.iter.ExactSizeIteratorSliceIter.len self.fst
  let b ← core.slice.iter.ExactSizeIteratorSliceIter.len self.snd
  ok (if a.val ≤ b.val then a else b)

@[reducible]
def core.iter.traits.exact_size.ExactSizeIteratorSliceZip (A B : Type) :
    core.iter.traits.exact_size.ExactSizeIterator
      (core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) (A × B) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceZip A B
  len := core.iter.adapters.zip.SliceZip.len
}

@[reducible]
def core.iter.traits.double_ended.DoubleEndedIteratorSliceZip (A B : Type) :
    core.iter.traits.double_ended.DoubleEndedIterator
      (core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) (A × B) := {
  iteratorInst := core.iter.traits.iterator.IteratorSliceZip A B
  next_back := ZipBack.sliceNext
  rfold := core.iter.adapters.zip.Zip.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorPair.rfold
    (core.iter.traits.double_ended.DoubleEndedIteratorSliceIter A)
    (core.iter.traits.exact_size.ExactSizeIteratorSliceIter A)
    (core.iter.traits.double_ended.DoubleEndedIteratorSliceIter B)
    (core.iter.traits.exact_size.ExactSizeIteratorSliceIter B)
}

namespace ZipBack

theorem slice_len_contents {A B : Type}
    (self : core.iter.adapters.zip.Zip (core.slice.iter.Iter A) (core.slice.iter.Iter B)) :
    ∃ len, core.iter.adapters.zip.SliceZip.len self = ok len ∧
      len.val = (self.fst.remaining.zip self.snd.remaining).length := by
  obtain ⟨a, ha, va⟩ := IteratorPrototype.slice_len_contents self.fst
  obtain ⟨b, hb, vb⟩ := IteratorPrototype.slice_len_contents self.snd
  unfold core.iter.adapters.zip.SliceZip.len
  simp only [ha, hb, bind_tc_ok]
  split
  next h => exact ⟨_, rfl, by simp only [List.length_zip]; omega⟩
  next h => exact ⟨_, rfl, by simp only [List.length_zip]; omega⟩

end ZipBack
end
end Aeneas.Std
