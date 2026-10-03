module
public import SliceFirst
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.WP
namespace slice_first.tests

theorem first_spec {T : Type} (xs : Slice T) :
    first xs = .ok xs.val.head? := rfl

theorem first_or_spec (xs : Slice U32) (fallback : U32) :
    first_or xs fallback = .ok (xs.val.head?.getD fallback) := by
  simp only [first_or, core.slice.Slice.first, bind_ok]
  cases xs.val.head? <;> rfl

#print axioms core.slice.Slice.first_spec
#print axioms core.slice.Slice.first_none_iff
#print axioms core.slice.Slice.first_getElem
#print axioms first_spec
#print axioms first_or_spec
end slice_first.tests
