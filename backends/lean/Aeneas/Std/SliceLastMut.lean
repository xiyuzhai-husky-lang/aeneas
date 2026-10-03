module
public import Aeneas.Std.Slice
public section

namespace Aeneas.Std
open Result

/-- Return the selected last mutable element to its original slice. As in
`SliceIndex::get_mut`, a missing returned borrow leaves the slice unchanged. -/
@[expose]
def core.slice.Slice.last_mut_back {T : Type} (s : Slice T) (value : Option T) : Slice T :=
  match value with
  | none => s
  | some value => s.setAtNat (s.val.length - 1) value

/-- Native `[.., last]` selection, with its original slice reconstruction. -/
@[expose, rust_fun "core::slice::{[@T]}::last_mut"]
def core.slice.Slice.last_mut {T : Type} (s : Slice T) :
    Result (Option T × (Option T → Slice T)) :=
  ok (s.val.getLast?, last_mut_back s)

@[simp] theorem core.slice.Slice.last_mut_exact {T : Type} (s : Slice T) :
    last_mut s = ok (s.val.getLast?, last_mut_back s) := rfl

@[simp] theorem core.slice.Slice.last_mut_back_none {T : Type} (s : Slice T) :
    last_mut_back s none = s := rfl

@[simp] theorem core.slice.Slice.last_mut_back_some_val {T : Type} (s : Slice T) (value : T) :
    (last_mut_back s (some value)).val = s.val.set (s.val.length - 1) value := by
  simp [last_mut_back, Slice.setAtNat]

@[simp] theorem core.slice.Slice.last_mut_back_length {T : Type} (s : Slice T) (value : Option T) :
    (last_mut_back s value).val.length = s.val.length := by
  cases value <;> simp [last_mut_back, Slice.setAtNat]

theorem core.slice.Slice.last_mut_back_last {T : Type} (s : Slice T) (value : T)
    (h : 0 < s.val.length) :
    (last_mut_back s (some value)).val[s.val.length - 1]'(by
      simp only [last_mut_back_length]; omega) = value := by
  exact Slice.getElem_Nat_setAtNat_eq s (s.val.length - 1) value (by
    change s.val.length - 1 < s.val.length
    omega)

theorem core.slice.Slice.last_mut_back_prefix {T : Type} (s : Slice T) (value : T)
    (i : Nat) (h : i < s.val.length - 1) :
    (last_mut_back s (some value)).val[i]'(by
      simp only [last_mut_back_length]; omega) = s.val[i]'(by omega) := by
  exact Slice.getElem_Nat_setAtNat_ne s (s.val.length - 1) i value (by
    change s.val.length - 1 ≠ i ∧ i < s.val.length
    omega)

end Aeneas.Std
