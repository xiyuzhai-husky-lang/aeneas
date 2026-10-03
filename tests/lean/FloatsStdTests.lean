module
public import FloatsStd
@[expose] public section
open Aeneas Aeneas.Std
namespace floats_std.tests

theorem clone32_preserves_bits (x : F32) : clone32 x = .ok x := rfl

theorem default32_positive_zero : default32 = .ok (F32.ofBits 0) := rfl

theorem infinity32_bits : infinity32 = .ok (F32.ofBits 0x7f800000) := rfl

theorem compare32_self (x : F32) (h : x.isNaN = false) :
    partial_cmp32 x x = .ok (some .eq) := by
  simp [partial_cmp32, F32.partial_cmp, BinaryFloat.partialCmp_eq_self x h]

theorem compare32_nan_left (x y : F32) (h : x.isNaN = true) :
    partial_cmp32 x y = .ok none := by
  simp [partial_cmp32, F32.partial_cmp, BinaryFloat.partialCmp, h]

theorem compare32_nan_right (x y : F32) (h : y.isNaN = true) :
    partial_cmp32 x y = .ok none := by
  simp [partial_cmp32, F32.partial_cmp, BinaryFloat.partialCmp, h]

theorem compare32_observation (x x' y y' : F32)
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    partial_cmp32 x y = partial_cmp32 x' y' := by
  unfold partial_cmp32 F32.partial_cmp
  rw [BinaryFloat.ObsEq.partialCmp_congr hx hy]

theorem compare32_zeros : partial_cmp32 (F32.ofBits 0) (F32.ofBits 0x80000000) =
    .ok (some .eq) := rfl

theorem compare32_negative : partial_cmp32 (F32.ofBits 0xbf800000) (F32.ofBits 0) =
    .ok (some .lt) := rfl

theorem clone64_preserves_bits (x : F64) : clone64 x = .ok x := rfl

theorem default64_positive_zero : default64 = .ok (F64.ofBits 0) := rfl

theorem infinity64_bits : infinity64 = .ok (F64.ofBits 0x7ff0000000000000) := rfl

theorem compare64_self (x : F64) (h : x.isNaN = false) :
    partial_cmp64 x x = .ok (some .eq) := by
  simp [partial_cmp64, F64.partial_cmp, BinaryFloat.partialCmp_eq_self x h]

theorem compare64_nan_left (x y : F64) (h : x.isNaN = true) :
    partial_cmp64 x y = .ok none := by
  simp [partial_cmp64, F64.partial_cmp, BinaryFloat.partialCmp, h]

theorem compare64_nan_right (x y : F64) (h : y.isNaN = true) :
    partial_cmp64 x y = .ok none := by
  simp [partial_cmp64, F64.partial_cmp, BinaryFloat.partialCmp, h]

theorem compare64_observation (x x' y y' : F64)
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    partial_cmp64 x y = partial_cmp64 x' y' := by
  unfold partial_cmp64 F64.partial_cmp
  rw [BinaryFloat.ObsEq.partialCmp_congr hx hy]

theorem compare64_zeros : partial_cmp64 (F64.ofBits 0) (F64.ofBits 0x8000000000000000) =
    .ok (some .eq) := rfl

theorem compare64_negative : partial_cmp64 (F64.ofBits 0xbff0000000000000) (F64.ofBits 0) =
    .ok (some .lt) := rfl

#print axioms clone32_preserves_bits
#print axioms default32_positive_zero
#print axioms infinity32_bits
#print axioms compare32_self
#print axioms compare32_nan_left
#print axioms compare32_nan_right
#print axioms compare32_observation
#print axioms compare32_zeros
#print axioms compare32_negative
#print axioms clone64_preserves_bits
#print axioms default64_positive_zero
#print axioms infinity64_bits
#print axioms compare64_self
#print axioms compare64_nan_left
#print axioms compare64_nan_right
#print axioms compare64_observation
#print axioms compare64_zeros
#print axioms compare64_negative
#print axioms BinaryFloat.partialCmp_none_iff
#print axioms BinaryFloat.partialCmp_eq_self
#print axioms BinaryFloat.ObsEq.partialCmp_congr
end floats_std.tests
