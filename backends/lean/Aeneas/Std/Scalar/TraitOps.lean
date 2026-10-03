module
public import Aeneas.Std.Scalar

/-!
Owned u32 operator trait methods use the same checked arithmetic and bit-vector
semantics as Aeneas's translation of direct primitive operators. In particular,
shifts check the shift count, not whether significant bits are shifted out.
-/
@[expose] public section
namespace Aeneas.Std
open Result WP
namespace U32

@[rust_fun "core::ops::arith::{core::ops::arith::Add<u32, u32, u32>}::add"]
def traitAdd (x y : U32) : Result U32 := x + y

@[rust_fun "core::ops::arith::{core::ops::arith::Sub<u32, u32, u32>}::sub"]
def traitSub (x y : U32) : Result U32 := x - y

@[rust_fun "core::ops::arith::{core::ops::arith::Rem<u32, u32, u32>}::rem"]
def traitRem (x y : U32) : Result U32 := x % y

@[rust_fun "core::ops::bit::{core::ops::bit::Not<u32, u32>}::not"]
def traitNot (x : U32) : Result U32 := .ok (~~~x)

@[rust_fun "core::ops::bit::{core::ops::bit::BitAnd<u32, u32, u32>}::bitand"]
def traitAnd (x y : U32) : Result U32 := .ok (x &&& y)

@[rust_fun "core::ops::bit::{core::ops::bit::BitOr<u32, u32, u32>}::bitor"]
def traitOr (x y : U32) : Result U32 := .ok (x ||| y)

@[rust_fun "core::ops::bit::{core::ops::bit::BitXor<u32, u32, u32>}::bitxor"]
def traitXor (x y : U32) : Result U32 := .ok (x ^^^ y)

@[rust_fun "core::ops::bit::{core::ops::bit::Shl<u32, usize, u32>}::shl"]
def traitShl (x : U32) (n : Usize) : Result U32 := x <<< n

@[rust_fun "core::ops::bit::{core::ops::bit::Shr<u32, usize, u32>}::shr"]
def traitShr (x : U32) (n : Usize) : Result U32 := x >>> n

@[step] theorem traitAdd_spec (x y : U32) (h : x.val + y.val ≤ U32.max) :
    traitAdd x y ⦃ z => z.val = x.val + y.val ∧ z.bv = x.bv + y.bv ⦄ :=
  U32.add_bv_spec h

theorem traitAdd_no_success_on_overflow (x y : U32) (h : U32.max < x.val + y.val)
    (z : U32) : traitAdd x y ≠ .ok z := by
  intro heq
  have hs := UScalar.add_equiv x y
  change (x + y : Result U32) = Result.ok z at heq
  simp [heq] at hs
  scalar_tac

@[step] theorem traitSub_spec (x y : U32) (h : y.val ≤ x.val) :
    traitSub x y ⦃ z => z.val = x.val - y.val ∧ z.bv = x.bv - y.bv ⦄ := by
  apply WP.spec_mono (U32.sub_bv_spec h)
  intro z hz
  exact ⟨hz.1, hz.2.2⟩

theorem traitSub_underflow (x y : U32) (h : x.val < y.val) :
    traitSub x y = .fail .integerOverflow := by
  simp [traitSub, HSub.hSub, UScalar.sub, h]

@[step] theorem traitRem_spec (x y : U32) (h : y.val ≠ 0) :
    traitRem x y ⦃ z => z.val = x.val % y.val ⦄ := U32.rem_spec x h

theorem traitRem_zero (x y : U32) (h : y.val = 0) :
    traitRem x y = .fail .divisionByZero := by
  simp [traitRem, HMod.hMod, UScalar.rem, h]

@[step] theorem traitNot_spec (x : U32) :
    traitNot x ⦃ z => z.bv = ~~~x.bv ⦄ := by simp [traitNot]

@[step] theorem traitAnd_spec (x y : U32) :
    traitAnd x y ⦃ z => z.bv = x.bv &&& y.bv ⦄ := by simp [traitAnd]

@[step] theorem traitOr_spec (x y : U32) :
    traitOr x y ⦃ z => z.bv = x.bv ||| y.bv ⦄ := by simp [traitOr]

@[step] theorem traitXor_spec (x y : U32) :
    traitXor x y ⦃ z => z.bv = x.bv ^^^ y.bv ⦄ := by simp [traitXor]

@[step] theorem traitShl_spec (x : U32) (n : Usize) (h : n.val < 32) :
    traitShl x n ⦃ z => z.val = (x.val <<< n.val) % U32.size ∧
      z.bv = x.bv <<< n.val ⦄ := U32.ShiftLeft_spec x n h

@[step] theorem traitShr_spec (x : U32) (n : Usize) (h : n.val < 32) :
    traitShr x n ⦃ z => z.val = x.val >>> n.val ∧
      z.bv = x.bv >>> n.val ⦄ := U32.ShiftRight_spec x n h

theorem traitShl_overflow (x : U32) (n : Usize) (h : 32 ≤ n.val) :
    traitShl x n = .fail .integerOverflow := by
  simp [traitShl, HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar,
    UScalar.shiftLeft, Nat.not_lt.mpr h]

theorem traitShr_overflow (x : U32) (n : Usize) (h : 32 ≤ n.val) :
    traitShr x n = .fail .integerOverflow := by
  simp [traitShr, HShiftRight.hShiftRight, UScalar.shiftRight_UScalar,
    UScalar.shiftRight, Nat.not_lt.mpr h]

end U32
end Aeneas.Std
