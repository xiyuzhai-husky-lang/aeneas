module
public import Floats

public section
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
set_option exponentiation.threshold 4096
namespace floats.casts

theorem to_int_nan : f64_to_i32 (F64.ofBits 0x7ff0000000000001) = .ok ⟨0⟩ := by rfl
theorem to_uint_negative : f32_to_u32 (F32.ofBits 0xbf800000) = .ok ⟨0⟩ := by rfl
theorem to_int_pos_inf : f32_to_i32 (F32.ofBits 0x7f800000) = .ok ⟨0x7fffffff⟩ := by rfl
theorem to_int_neg_inf : f64_to_i32 (F64.ofBits 0xfff0000000000000) = .ok ⟨0x80000000⟩ := by rfl
theorem to_uint_inf : f64_to_u64 (F64.ofBits 0x7ff0000000000000) = .ok ⟨0xffffffffffffffff⟩ := by rfl
theorem truncate_negative : f32_to_i32 (F32.ofBits 0xbfc00000) = .ok ⟨0xffffffff⟩ := by rfl
theorem truncate_subnormal : f64_to_i64 (F64.ofBits 1) = .ok ⟨0⟩ := by rfl
theorem saturate_i32 : f64_to_i32 (F64.ofBits 0x41e0000000000000) = .ok ⟨0x7fffffff⟩ := by rfl
theorem int_tie_even : u32_to_f32 ⟨0x01000001⟩ = .ok (F32.ofBits 0x4b800000) := by rfl
theorem int_tie_odd : u32_to_f32 ⟨0x01000003⟩ = .ok (F32.ofBits 0x4b800002) := by rfl
theorem int_negative : i32_to_f64 ⟨0xffffffff⟩ = .ok (F64.ofBits 0xbff0000000000000) := by rfl
theorem uint128_overflow : u128_to_f32 ⟨0xffffffffffffffffffffffffffffffff⟩ = .ok (F32.ofBits 0x7f800000) := by rfl
theorem widen_subnormal : f32_to_f64 (F32.ofBits 1) = .ok (F64.ofBits 0x36a0000000000000) := by rfl
theorem narrow_underflow : f64_to_f32 (F64.ofBits 1) = .ok (F32.ofBits 0) := by rfl
theorem narrow_overflow : f64_to_f32 (F64.ofBits 0x7fefffffffffffff) = .ok (F32.ofBits 0x7f800000) := by rfl
theorem narrow_tie_even : f64_to_f32 (F64.ofBits 0x3ff0000010000000) = .ok (F32.ofBits 0x3f800000) := by rfl

#print axioms to_int_nan
#print axioms to_uint_negative
#print axioms to_int_pos_inf
#print axioms to_int_neg_inf
#print axioms to_uint_inf
#print axioms truncate_negative
#print axioms truncate_subnormal
#print axioms saturate_i32
#print axioms int_tie_even
#print axioms int_tie_odd
#print axioms int_negative
#print axioms uint128_overflow
#print axioms widen_subnormal
#print axioms narrow_underflow
#print axioms narrow_overflow
#print axioms narrow_tie_even
#print axioms BinaryFloat.toUScalar_nan
#print axioms BinaryFloat.toIScalar_nan
#print axioms BinaryFloat.toUScalar_finite
#print axioms BinaryFloat.toIScalar_finite_in_range
#print axioms BinaryFloat.ObsEq.toUScalar_congr
#print axioms BinaryFloat.ObsEq.toIScalar_congr
#print axioms BinaryFloat.ObsEq.convert_congr
end floats.casts
