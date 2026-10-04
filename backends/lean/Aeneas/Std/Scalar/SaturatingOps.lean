module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Saturating Operations
-/

/-!
Saturating add: unsigned
-/
def UScalar.saturating_add {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Min.min (UScalar.max ty) (x.val + y.val)) ⟩

/- [core::num::{u8}::saturating_add] -/
uscalar def core.num.«%S».saturating_add := @UScalar.saturating_add UScalarTy.«%S»

/-!
Saturating add: signed
-/
def IScalar.saturating_add {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val + y.val))) ⟩

/- [core::num::{i8}::saturating_add] -/
iscalar def core.num.«%S».saturating_add := @IScalar.saturating_add IScalarTy.«%S»

/-!
Saturating sub: unsigned
-/
def UScalar.saturating_sub {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Max.max 0 (x.val - y.val)) ⟩

/- [core::num::{u8}::saturating_sub] -/
uscalar def core.num.«%S».saturating_sub := @UScalar.saturating_sub UScalarTy.«%S»

/-!
Saturating sub: signed
-/
def IScalar.saturating_sub {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val - y.val))) ⟩

/- [core::num::{i8}::saturating_sub] -/
iscalar def core.num.«%S».saturating_sub := @IScalar.saturating_sub IScalarTy.«%S»

def UScalar.saturating_mul {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨BitVec.ofNat _ (min (UScalar.max ty) (x.val * y.val))⟩

theorem UScalar.saturating_mul_val {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_mul x y).val = min (UScalar.max ty) (x.val * y.val) := by
  simp only [UScalar.saturating_mul,UScalar.val,BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound : UScalar.max ty < 2 ^ ty.numBits := by
    rw [UScalar.max]
    have positive : 0 < 2 ^ ty.numBits := Nat.two_pow_pos ty.numBits
    omega
  exact lt_of_le_of_lt (Nat.min_le_left _ _) bound

/- [core::num::{usize}::saturating_mul] -/
@[rust_fun "core::num::{usize}::saturating_mul"]
def core.num.Usize.saturating_mul := @UScalar.saturating_mul .Usize

end Aeneas.Std
