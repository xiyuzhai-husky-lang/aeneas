module
public import Aeneas.Std.Array.ArraySlice
public section

@[expose] section
namespace Aeneas.Std
open Result

@[rust_trait "core::slice::SlicePattern"]
structure core.slice.SlicePattern (Self Item : Type) where
  as_slice : Self → Result (Slice Item)

@[rust_fun "core::slice::{core::slice::SlicePattern<[@T; @N], @T>}::as_slice"]
def Array.Insts.CoreSliceSlicePattern.as_slice {T : Type} {N : Usize}
    (self : Array T N) : Result (Slice T) := ok self.to_slice

@[rust_trait_impl "core::slice::SlicePattern<[@T; @N], @T>"]
def Array.Insts.CoreSliceSlicePattern (T : Type) (N : Usize) :
    core.slice.SlicePattern (Array T N) T where
  as_slice := Array.Insts.CoreSliceSlicePattern.as_slice

@[rust_fun "core::slice::{core::slice::SlicePattern<[@T], @T>}::as_slice"]
def Slice.Insts.CoreSliceSlicePattern.as_slice {T : Type}
    (self : Slice T) : Result (Slice T) := ok self

@[rust_trait_impl "core::slice::SlicePattern<[@T], @T>"]
def Slice.Insts.CoreSliceSlicePattern (T : Type) : core.slice.SlicePattern (Slice T) T where
  as_slice := Slice.Insts.CoreSliceSlicePattern.as_slice

/-- Exact head and tail at the needle length, with the original element order.
They are bounded slices even when the needle is longer than the input; the
native caller checks lengths before invoking equality. -/
def SlicePrefixModel.head {T : Type} (self needle : Slice T) : Slice T :=
  .from (self.val.take needle.val.length)
    (by have := self.property; simp only [List.length_take]; omega)

def SlicePrefixModel.tail {T : Type} (self needle : Slice T) : Slice T :=
  .from (self.val.drop needle.val.length)
    (by have := self.property; simp only [List.length_drop]; omega)

/-- Native `strip_prefix`: obtain the pattern once, reject a longer pattern
without equality calls, then compare the original head to that pattern.
The ordinary slice equality model retains its callback order and failures. -/
@[rust_fun "core::slice::{[@T]}::strip_prefix"]
def core.slice.Slice.strip_prefix {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) : Result (Option (Slice T)) := do
  let needle ← pattern.as_slice needle
  if needle.val.length ≤ self.val.length then
    let accepted ← core.slice.cmp.PartialEqSlice.eq cmp (SlicePrefixModel.head self needle) needle
    if accepted then ok (some (SlicePrefixModel.tail self needle)) else ok none
  else ok none

namespace SlicePrefixModel

@[simp] theorem head_val {T : Type} (self needle : Slice T) :
    (head self needle).val = self.val.take needle.val.length := by simp [head]

@[simp] theorem tail_val {T : Type} (self needle : Slice T) :
    (tail self needle).val = self.val.drop needle.val.length := by simp [tail]

theorem strip_prefix_too_long {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T)
    (converted : pattern.as_slice needle = ok slice) (longer : self.val.length < slice.val.length) :
    core.slice.Slice.strip_prefix pattern cmp self needle = ok none := by
  simp [core.slice.Slice.strip_prefix,converted,Nat.not_le.mpr longer]

theorem strip_prefix_some {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T)
    (converted : pattern.as_slice needle = ok slice) (fits : slice.val.length ≤ self.val.length)
    (equal : core.slice.cmp.PartialEqSlice.eq cmp (head self slice) slice = ok true) :
    core.slice.Slice.strip_prefix pattern cmp self needle = ok (some (tail self slice)) := by
  simp [core.slice.Slice.strip_prefix,converted,fits,equal]

theorem strip_prefix_mismatch {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T)
    (converted : pattern.as_slice needle = ok slice) (fits : slice.val.length ≤ self.val.length)
    (different : core.slice.cmp.PartialEqSlice.eq cmp (head self slice) slice = ok false) :
    core.slice.Slice.strip_prefix pattern cmp self needle = ok none := by
  simp [core.slice.Slice.strip_prefix,converted,fits,different]

theorem strip_prefix_pattern_fail {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (error : Error)
    (failed : pattern.as_slice needle = fail error) :
    core.slice.Slice.strip_prefix pattern cmp self needle = fail error := by
  simp [core.slice.Slice.strip_prefix,failed]

theorem strip_prefix_pattern_div {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P)
    (diverged : pattern.as_slice needle = div) :
    core.slice.Slice.strip_prefix pattern cmp self needle = div := by
  simp [core.slice.Slice.strip_prefix,diverged]

theorem strip_prefix_comparison_fail {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T) (error : Error)
    (converted : pattern.as_slice needle = ok slice) (fits : slice.val.length ≤ self.val.length)
    (failed : core.slice.cmp.PartialEqSlice.eq cmp (head self slice) slice = fail error) :
    core.slice.Slice.strip_prefix pattern cmp self needle = fail error := by
  simp [core.slice.Slice.strip_prefix,converted,fits,failed]

theorem strip_prefix_comparison_div {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T)
    (converted : pattern.as_slice needle = ok slice) (fits : slice.val.length ≤ self.val.length)
    (diverged : core.slice.cmp.PartialEqSlice.eq cmp (head self slice) slice = div) :
    core.slice.Slice.strip_prefix pattern cmp self needle = div := by
  simp [core.slice.Slice.strip_prefix,converted,fits,diverged]

/-- The empty pattern returns the original slice and makes no element-equality
calls, even for an arbitrary `PartialEq` implementation. -/
theorem strip_prefix_empty {T P : Type} (pattern : core.slice.SlicePattern P T)
    (cmp : core.cmp.PartialEq T T) (self : Slice T) (needle : P) (slice : Slice T)
    (converted : pattern.as_slice needle = ok slice) (empty : slice.val = []) :
    core.slice.Slice.strip_prefix pattern cmp self needle = ok (some self) := by
  have remainder : tail self slice = self := by apply Slice.ext; simp [empty]
  have equal : core.slice.cmp.PartialEqSlice.eq cmp (head self slice) slice = ok true := by
    simp [core.slice.cmp.PartialEqSlice.eq,empty,head]
    rfl
  simpa [remainder] using strip_prefix_some pattern cmp self needle slice converted
    (by simp [empty]) equal

theorem array_pattern_contents {T : Type} {N : Usize} (self : Array T N) :
    Array.Insts.CoreSliceSlicePattern.as_slice self = ok self.to_slice ∧
      self.to_slice.val = self.val := ⟨rfl,by simp⟩

end SlicePrefixModel
end Aeneas.Std
