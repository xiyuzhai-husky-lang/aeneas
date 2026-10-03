module
public import Aeneas.Std.Slice
@[expose] public section

namespace Aeneas.Std
open Result WP

/-- Shared access to the last logical element; empty slices return `none`.
    As for other shared-borrow models, the returned reference is its value. -/
@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type} (s : Slice T) : Result (Option T) :=
  ok s.val.getLast?

@[step]
theorem core.slice.Slice.last_spec {T : Type} (s : Slice T) :
    core.slice.Slice.last s ⦃ r => r = s.val.getLast? ⦄ := by
  simp only [core.slice.Slice.last, spec_ok]

theorem core.slice.Slice.last_none_iff {T : Type} (s : Slice T) :
    core.slice.Slice.last s = ok none ↔ s.val = [] := by
  simp only [core.slice.Slice.last, ok.injEq, List.getLast?_eq_none_iff]

theorem core.slice.Slice.last_getElem {T : Type} (s : Slice T)
    (h : 0 < s.val.length) :
    core.slice.Slice.last s = ok (some (s.val[s.val.length - 1]'(by scalar_tac))) := by
  simp only [core.slice.Slice.last, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by scalar_tac : s.val.length - 1 < s.val.length)]
end Aeneas.Std
