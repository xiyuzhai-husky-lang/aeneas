module
public import Floats
public import Aeneas.Std.FloatLemmas

public section
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace floats.arithmetic

-- Kernel-checked boundary results of the extracted Rust functions.
-- These concrete proofs supplement the universal rounding and observation
-- lemmas; they do not replace the outstanding whole IEEE refinement proof.

theorem add_tie_even32 : add32 (F32.ofBits 0x3f800000) (F32.ofBits 0x33800000) =
    .ok (F32.ofBits 0x3f800000) := by rfl

theorem add_tie_odd32 : add32 (F32.ofBits 0x3f800001) (F32.ofBits 0x33800000) =
    .ok (F32.ofBits 0x3f800002) := by rfl

theorem cancel32 : add32 (F32.ofBits 0xbf800000) (F32.ofBits 0x3f800000) =
    .ok (F32.ofBits 0x0) := by rfl

theorem negative_zeros32 : add32 (F32.ofBits 0x80000000) (F32.ofBits 0x80000000) =
    .ok (F32.ofBits 0x80000000) := by rfl

theorem subtract32 : sub32 (F32.ofBits 0x3f800000) (F32.ofBits 0x3f800000) =
    .ok (F32.ofBits 0x0) := by rfl

theorem underflow_even32 : mul32 (F32.ofBits 0x1) (F32.ofBits 0x3f000000) =
    .ok (F32.ofBits 0x0) := by rfl

theorem underflow_odd32 : mul32 (F32.ofBits 0x3) (F32.ofBits 0x3f000000) =
    .ok (F32.ofBits 0x2) := by rfl

theorem overflow32 : mul32 (F32.ofBits 0x7f7fffff) (F32.ofBits 0x40000000) =
    .ok (F32.ofBits 0x7f800000) := by rfl

theorem third32 : div32 (F32.ofBits 0x3f800000) (F32.ofBits 0x40400000) =
    .ok (F32.ofBits 0x3eaaaaab) := by rfl

theorem subnormal32 : div32 (F32.ofBits 0x800000) (F32.ofBits 0x40000000) =
    .ok (F32.ofBits 0x400000) := by rfl

theorem remainder32 : rem32 (F32.ofBits 0xc0b00000) (F32.ofBits 0x40000000) =
    .ok (F32.ofBits 0xbfc00000) := by rfl

theorem signed_zero_product32 : mul32 (F32.ofBits 0x80000000) (F32.ofBits 0x40000000) =
    .ok (F32.ofBits 0x80000000) := by rfl

theorem negative_infinity32 : div32 (F32.ofBits 0x3f800000) (F32.ofBits 0x80000000) =
    .ok (F32.ofBits 0xff800000) := by rfl

theorem zero_div_zero32 :
    div32 (F32.ofBits 0) (F32.ofBits 0) = .ok BinaryFloat.nan ∧
    (BinaryFloat.nan : F32).isNaN = true := by exact ⟨rfl, rfl⟩

theorem add32_observations {x x' y y' : F32}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    add32 x y = add32 x' y' := by
  simp only [add32, F32.add, hx.add_congr hy]

theorem sub32_observations {x x' y y' : F32}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    sub32 x y = sub32 x' y' := by
  simp only [sub32, F32.sub, hx.sub_congr hy]

theorem mul32_observations {x x' y y' : F32}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    mul32 x y = mul32 x' y' := by
  simp only [mul32, F32.mul, hx.mul_congr hy]

theorem div32_observations {x x' y y' : F32}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    div32 x y = div32 x' y' := by
  simp only [div32, F32.div, hx.div_congr hy]

theorem rem32_observations {x x' y y' : F32}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    rem32 x y = rem32 x' y' := by
  simp only [rem32, F32.rem, hx.rem_congr hy]

theorem add_tie_even64 : add64 (F64.ofBits 0x3ff0000000000000) (F64.ofBits 0x3ca0000000000000) =
    .ok (F64.ofBits 0x3ff0000000000000) := by rfl

theorem add_tie_odd64 : add64 (F64.ofBits 0x3ff0000000000001) (F64.ofBits 0x3ca0000000000000) =
    .ok (F64.ofBits 0x3ff0000000000002) := by rfl

theorem cancel64 : add64 (F64.ofBits 0xbff0000000000000) (F64.ofBits 0x3ff0000000000000) =
    .ok (F64.ofBits 0x0) := by rfl

theorem negative_zeros64 : add64 (F64.ofBits 0x8000000000000000) (F64.ofBits 0x8000000000000000) =
    .ok (F64.ofBits 0x8000000000000000) := by rfl

theorem subtract64 : sub64 (F64.ofBits 0x3ff0000000000000) (F64.ofBits 0x3ff0000000000000) =
    .ok (F64.ofBits 0x0) := by rfl

theorem underflow_even64 : mul64 (F64.ofBits 0x1) (F64.ofBits 0x3fe0000000000000) =
    .ok (F64.ofBits 0x0) := by rfl

theorem underflow_odd64 : mul64 (F64.ofBits 0x3) (F64.ofBits 0x3fe0000000000000) =
    .ok (F64.ofBits 0x2) := by rfl

theorem overflow64 : mul64 (F64.ofBits 0x7fefffffffffffff) (F64.ofBits 0x4000000000000000) =
    .ok (F64.ofBits 0x7ff0000000000000) := by rfl

theorem third64 : div64 (F64.ofBits 0x3ff0000000000000) (F64.ofBits 0x4008000000000000) =
    .ok (F64.ofBits 0x3fd5555555555555) := by rfl

theorem subnormal64 : div64 (F64.ofBits 0x10000000000000) (F64.ofBits 0x4000000000000000) =
    .ok (F64.ofBits 0x8000000000000) := by rfl

theorem remainder64 : rem64 (F64.ofBits 0xc016000000000000) (F64.ofBits 0x4000000000000000) =
    .ok (F64.ofBits 0xbff8000000000000) := by rfl

theorem signed_zero_product64 : mul64 (F64.ofBits 0x8000000000000000) (F64.ofBits 0x4000000000000000) =
    .ok (F64.ofBits 0x8000000000000000) := by rfl

theorem negative_infinity64 : div64 (F64.ofBits 0x3ff0000000000000) (F64.ofBits 0x8000000000000000) =
    .ok (F64.ofBits 0xfff0000000000000) := by rfl

theorem zero_div_zero64 :
    div64 (F64.ofBits 0) (F64.ofBits 0) = .ok BinaryFloat.nan ∧
    (BinaryFloat.nan : F64).isNaN = true := by exact ⟨rfl, rfl⟩

theorem add64_observations {x x' y y' : F64}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    add64 x y = add64 x' y' := by
  simp only [add64, F64.add, hx.add_congr hy]

theorem sub64_observations {x x' y y' : F64}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    sub64 x y = sub64 x' y' := by
  simp only [sub64, F64.sub, hx.sub_congr hy]

theorem mul64_observations {x x' y y' : F64}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    mul64 x y = mul64 x' y' := by
  simp only [mul64, F64.mul, hx.mul_congr hy]

theorem div64_observations {x x' y y' : F64}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    div64 x y = div64 x' y' := by
  simp only [div64, F64.div, hx.div_congr hy]

theorem rem64_observations {x x' y y' : F64}
    (hx : BinaryFloat.ObsEq x x') (hy : BinaryFloat.ObsEq y y') :
    rem64 x y = rem64 x' y' := by
  simp only [rem64, F64.rem, hx.rem_congr hy]

#print axioms add_tie_even32
#print axioms add_tie_odd32
#print axioms cancel32
#print axioms negative_zeros32
#print axioms subtract32
#print axioms underflow_even32
#print axioms underflow_odd32
#print axioms overflow32
#print axioms third32
#print axioms subnormal32
#print axioms remainder32
#print axioms signed_zero_product32
#print axioms negative_infinity32
#print axioms zero_div_zero32
#print axioms add32_observations
#print axioms sub32_observations
#print axioms mul32_observations
#print axioms div32_observations
#print axioms rem32_observations
#print axioms add_tie_even64
#print axioms add_tie_odd64
#print axioms cancel64
#print axioms negative_zeros64
#print axioms subtract64
#print axioms underflow_even64
#print axioms underflow_odd64
#print axioms overflow64
#print axioms third64
#print axioms subnormal64
#print axioms remainder64
#print axioms signed_zero_product64
#print axioms negative_infinity64
#print axioms zero_div_zero64
#print axioms add64_observations
#print axioms sub64_observations
#print axioms mul64_observations
#print axioms div64_observations
#print axioms rem64_observations
#print axioms BinaryFloat.roundQuotient_bounds
#print axioms BinaryFloat.roundQuotient_half
#print axioms BinaryFloat.roundQuotient_tie_even
#print axioms BinaryFloat.magnitude_neg
#print axioms BinaryFloat.isNaN_neg
#print axioms BinaryFloat.ObsEq.refl
#print axioms BinaryFloat.ObsEq.symm
#print axioms BinaryFloat.ObsEq.trans
#print axioms BinaryFloat.ObsEq.eq_congr
#print axioms BinaryFloat.ObsEq.lt_congr
#print axioms BinaryFloat.ObsEq.neg_congr
#print axioms BinaryFloat.ObsEq.add_congr
#print axioms BinaryFloat.ObsEq.sub_congr
#print axioms BinaryFloat.ObsEq.mul_congr
#print axioms BinaryFloat.ObsEq.div_congr
#print axioms BinaryFloat.ObsEq.rem_congr
end floats.arithmetic
