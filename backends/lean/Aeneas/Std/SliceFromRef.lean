module
public import Aeneas.Std.Slice
public section

namespace Aeneas.Std

/-- Logical contents of Rust's `slice::from_ref`: one borrowed element,
without allocation or cloning. Pointer representation is the usual slice
library-model boundary. -/
@[expose, rust_fun "core::slice::raw::from_ref" -canFail -lift]
def core.slice.raw.from_ref {T : Type} (value : T) : Slice T :=
  Slice.from [value] (by simp; scalar_tac)

@[simp]
theorem core.slice.raw.from_ref_val {T : Type} (value : T) :
    (from_ref value).val = [value] := by simp [from_ref]

end Aeneas.Std
