module
public import Aeneas.Std.FloatLemmas
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default

@[expose] public section
namespace Aeneas.Std

namespace BinaryFloat
variable {e f : Nat}

/-- Rust PartialOrd reports NaNs as unordered and compares the signed zeros equal. -/
def partialCmp (x y : BinaryFloat e f) : Option Ordering :=
  if x.isNaN || y.isNaN then none
  else if eq x y then some .eq
  else if lt x y then some .lt
  else some .gt

@[simp] theorem partialCmp_none_iff (x y : BinaryFloat e f) :
    partialCmp x y = none ↔ x.isNaN = true ∨ y.isNaN = true := by
  cases hx : x.isNaN <;> cases hy : y.isNaN <;> simp [partialCmp, hx, hy]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem partialCmp_eq_self (x : BinaryFloat e f) (h : x.isNaN = false) :
    partialCmp x x = some .eq := by
  simp [partialCmp, h]

theorem ObsEq.partialCmp_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : partialCmp x y = partialCmp x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [partialCmp, hy, hy']
  · simp [partialCmp, hx, hx']
end BinaryFloat

@[rust_fun "core::clone::impls::{core::clone::Clone<f32>}::clone"]
def F32.clone (x : F32) : Result F32 := .ok x

@[rust_fun "core::default::{core::default::Default<f32>}::default"]
def F32.default : Result F32 := .ok (F32.ofBits 0)

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<f32, f32>}::partial_cmp"]
def F32.partial_cmp (x y : F32) : Result (Option Ordering) :=
  .ok (BinaryFloat.partialCmp x y)

@[rust_const "core::f32::{f32}::INFINITY" -canFail]
def F32.INFINITY : F32 := F32.ofBits 0x7f800000

@[rust_fun "core::clone::impls::{core::clone::Clone<f64>}::clone"]
def F64.clone (x : F64) : Result F64 := .ok x

@[rust_fun "core::default::{core::default::Default<f64>}::default"]
def F64.default : Result F64 := .ok (F64.ofBits 0)

@[rust_fun "core::cmp::impls::{core::cmp::PartialOrd<f64, f64>}::partial_cmp"]
def F64.partial_cmp (x y : F64) : Result (Option Ordering) :=
  .ok (BinaryFloat.partialCmp x y)

@[rust_const "core::f64::{f64}::INFINITY" -canFail]
def F64.INFINITY : F64 := F64.ofBits 0x7ff0000000000000

end Aeneas.Std
