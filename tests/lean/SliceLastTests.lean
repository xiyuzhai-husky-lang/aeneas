module
public import SliceLast
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.WP
namespace slice_last.tests

theorem last_spec {T : Type} (xs : Slice T) :
    last xs = .ok xs.val.getLast? := rfl

theorem last_or_spec (xs : Slice U32) (fallback : U32) :
    last_or xs fallback = .ok (xs.val.getLast?.getD fallback) := by
  simp only [last_or, core.slice.Slice.last, bind_ok]
  cases xs.val.getLast? <;> rfl

#print axioms core.slice.Slice.last_spec
#print axioms core.slice.Slice.last_none_iff
#print axioms core.slice.Slice.last_getElem
#print axioms last_spec
#print axioms last_or_spec
end slice_last.tests
