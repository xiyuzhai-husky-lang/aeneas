import Aeneas.Std.IteratorPredicates
open Aeneas.Std Aeneas.Std.Result

/-- Alternating front/back consumption returns 10, 30, 20, then exhaustion;
    the shortened-slice representation never returns a consumed item again. -/
theorem slice_iterator_mixed_ends :
    (do
      let initial ← core.slice.Slice.iter (Slice.from [10, 20, 30] (by scalar_tac))
      let a ← core.slice.iter.IteratorSliceIter.next initial
      let b ← core.slice.iter.IteratorSliceIter.next_back a.2
      let c ← core.slice.iter.IteratorSliceIter.next b.2
      let d ← core.slice.iter.IteratorSliceIter.next_back c.2
      .ok (a.1, b.1, c.1, d.1)) =
    .ok ((some 10 : Option Nat), some 30, some 20, none) := by
  simp [core.slice.Slice.iter, core.slice.iter.IteratorSliceIter.next,
    core.slice.iter.IteratorSliceIter.next_back]
  constructor <;> rfl

#print axioms core.iter.traits.iterator.Iterator.any.finite
#print axioms core.iter.traits.iterator.Iterator.all.finite
#print axioms core.slice.iter.IteratorSliceIter.next_back_empty
#print axioms core.slice.iter.IteratorSliceIter.next_back_nonempty
#print axioms slice_iterator_mixed_ends
