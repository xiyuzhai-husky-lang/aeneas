import Aeneas.Std.SearchSupport
open Aeneas.Std Aeneas.Std.Result

/-- Closing a mutable Vec borrow without modification reconstructs the original
    vector. The same return function writes any later iterator slice back. -/
theorem mutable_vec_iterator_borrow_roundtrip {T : Type} (v : alloc.vec.Vec T) :
    ∃ it back, MutVec.IntoIterator.into_iter v = .ok (it, back) ∧ back it = v := by
  refine ⟨⟨v.slice, 0⟩, (fun it => ⟨it.slice⟩), rfl, ?_⟩
  cases v
  rfl

#print axioms core.cmp.impls.OrdBool.cmp_correct
#print axioms core.cmp.Ordering.then_correct
#print axioms SharedVec.IntoIterator.into_iter_correct
#print axioms MutVec.IntoIterator.into_iter_correct
#print axioms alloc.vec.VecFromSlice.from_correct
#print axioms mutable_vec_iterator_borrow_roundtrip
