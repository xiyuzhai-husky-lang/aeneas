module
public import Aeneas.Std.Slice
@[expose] public section

namespace Aeneas.Std
open Result WP

/-- Shared access to the first logical element; empty slices return `none`.
    As for other shared-borrow models, the returned reference is its value. -/
@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type} (s : Slice T) : Result (Option T) :=
  ok s.val.head?

@[step]
theorem core.slice.Slice.first_spec {T : Type} (s : Slice T) :
    core.slice.Slice.first s ⦃ r => r = s.val.head? ⦄ := by
  simp only [core.slice.Slice.first, spec_ok]

theorem core.slice.Slice.first_none_iff {T : Type} (s : Slice T) :
    core.slice.Slice.first s = ok none ↔ s.val = [] := by
  simp only [core.slice.Slice.first, ok.injEq, List.head?_eq_none_iff]

theorem core.slice.Slice.first_getElem {T : Type} (s : Slice T)
    (h : 0 < s.val.length) :
    core.slice.Slice.first s = ok (some (s.val[0]'h)) := by
  simp only [core.slice.Slice.first, List.head?_eq_getElem?, List.getElem?_eq_getElem h]
end Aeneas.Std
