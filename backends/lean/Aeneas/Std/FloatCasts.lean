module
public import Aeneas.Std.Float
public import Aeneas.Std.Scalar.Core

/-!
Rust numeric float casts: nearest-even integer/float and float/float conversion,
and truncation with saturation (NaN maps to zero) for float/integer conversion.
NaN observations follow the arithmetic model; raw-payload conversions are absent.
-/
@[expose] public section
namespace Aeneas.Std
namespace BinaryFloat
variable {e f : Nat}

def fromUScalar {ty : UScalarTy} (x : UScalar ty) : BinaryFloat e f :=
  roundRatio false x.bv.toNat 1 0

def fromIScalar {ty : IScalarTy} (x : IScalar ty) : BinaryFloat e f :=
  roundRatio (decide (x.bv.toInt < 0)) x.bv.toInt.natAbs 1 0

/-- Truncate a finite float's magnitude toward zero. -/
def truncMagnitude (x : BinaryFloat e f) : Nat :=
  let (n, exponent) := x.finiteParts
  if exponent ≥ 0 then n * 2 ^ exponent.toNat
  else n / 2 ^ (-exponent).toNat

def toUScalar (ty : UScalarTy) (x : BinaryFloat e f) : UScalar ty :=
  let n := if x.isNaN || x.sign then 0
           else if x.isInf then 2 ^ ty.numBits - 1
           else min x.truncMagnitude (2 ^ ty.numBits - 1)
  ⟨BitVec.ofNat _ n⟩

def toIScalar (ty : IScalarTy) (x : BinaryFloat e f) : IScalar ty :=
  let bound : Int := 2 ^ (ty.numBits - 1)
  let n := if x.isNaN then 0
           else if x.isInf then (if x.sign then -bound else bound - 1)
           else
             let magnitude : Int := x.truncMagnitude
             max (-bound) (min (bound - 1) (if x.sign then -magnitude else magnitude))
  ⟨BitVec.ofInt _ n⟩

def convert (targetE targetF : Nat) (x : BinaryFloat e f) : BinaryFloat targetE targetF :=
  if x.isNaN then nan
  else if x.isInf then infinity x.sign
  else let (n, exponent) := x.finiteParts
       roundRatio x.sign n 1 exponent

@[simp] theorem toUScalar_nan (ty : UScalarTy) (x : BinaryFloat e f)
    (hx : x.isNaN = true) : toUScalar ty x = ⟨0⟩ := by
  simp [toUScalar, hx]
@[simp] theorem toIScalar_nan (ty : IScalarTy) (x : BinaryFloat e f)
    (hx : x.isNaN = true) : toIScalar ty x = ⟨0⟩ := by
  simp [toIScalar, hx]

theorem toUScalar_finite (ty : UScalarTy) (x : BinaryFloat e f)
    (hnan : x.isNaN = false) (hinf : x.isInf = false) (hsign : x.sign = false) :
    (toUScalar ty x).bv.toNat = min x.truncMagnitude (2 ^ ty.numBits - 1) := by
  have hp := Nat.two_pow_pos ty.numBits
  have hm := Nat.min_le_right x.truncMagnitude (2 ^ ty.numBits - 1)
  simp [toUScalar, hnan, hinf, hsign, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show min x.truncMagnitude (2 ^ ty.numBits - 1) < 2 ^ ty.numBits by omega)]

theorem toIScalar_finite_in_range (ty : IScalarTy) (x : BinaryFloat e f)
    (hnan : x.isNaN = false) (hinf : x.isInf = false)
    (lo : -(2 : Int) ^ (ty.numBits - 1) ≤
      if x.sign then -(x.truncMagnitude : Int) else x.truncMagnitude)
    (hi : (if x.sign then -(x.truncMagnitude : Int) else x.truncMagnitude) <
      (2 : Int) ^ (ty.numBits - 1)) :
    (toIScalar ty x).bv.toInt =
      if x.sign then -(x.truncMagnitude : Int) else x.truncMagnitude := by
  have hmax : (if x.sign then -(x.truncMagnitude : Int) else x.truncMagnitude) ≤
      (2 : Int) ^ (ty.numBits - 1) - 1 := by omega
  simp only [toIScalar, hnan, hinf, Bool.false_eq_true, if_false,
    min_eq_right hmax, max_eq_right lo]
  exact BitVec.toInt_ofInt_eq_self (by have := ty.numBits_nonzero; omega) lo hi

theorem ObsEq.toUScalar_congr {x y : BinaryFloat e f} (h : ObsEq x y)
    (ty : UScalarTy) : toUScalar ty x = toUScalar ty y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · simp [toUScalar, hx, hy]

theorem ObsEq.toIScalar_congr {x y : BinaryFloat e f} (h : ObsEq x y)
    (ty : IScalarTy) : toIScalar ty x = toIScalar ty y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · simp [toIScalar, hx, hy]

theorem ObsEq.convert_congr {x y : BinaryFloat e f} (h : ObsEq x y)
    (targetE targetF : Nat) : convert targetE targetF x = convert targetE targetF y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · simp [convert, hx, hy]
end BinaryFloat

namespace F32
def fromUScalar {ty : UScalarTy} (x : UScalar ty) : F32 := BinaryFloat.fromUScalar x
def fromIScalar {ty : IScalarTy} (x : IScalar ty) : F32 := BinaryFloat.fromIScalar x
def toUScalar (ty : UScalarTy) (x : F32) : UScalar ty := BinaryFloat.toUScalar ty x
def toIScalar (ty : IScalarTy) (x : F32) : IScalar ty := BinaryFloat.toIScalar ty x
def fromF32 (x : F32) : F32 := x
def fromF64 (x : F64) : F32 := BinaryFloat.convert 8 23 x
end F32

namespace F64
def fromUScalar {ty : UScalarTy} (x : UScalar ty) : F64 := BinaryFloat.fromUScalar x
def fromIScalar {ty : IScalarTy} (x : IScalar ty) : F64 := BinaryFloat.fromIScalar x
def toUScalar (ty : UScalarTy) (x : F64) : UScalar ty := BinaryFloat.toUScalar ty x
def toIScalar (ty : IScalarTy) (x : F64) : IScalar ty := BinaryFloat.toIScalar ty x
def fromF32 (x : F32) : F64 := BinaryFloat.convert 11 52 x
def fromF64 (x : F64) : F64 := x
end F64
end Aeneas.Std
