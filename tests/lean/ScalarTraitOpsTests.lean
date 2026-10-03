module
public import ScalarTraitOps
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace scalar_trait_ops.tests

theorem add_spec (x y : U32) (h : x.val + y.val ≤ U32.max) :
    add x y ⦃ z => z.val = x.val + y.val ∧ z.bv = x.bv + y.bv ⦄ :=
  U32.traitAdd_spec x y h

theorem add_no_success_on_overflow (x y : U32) (h : U32.max < x.val + y.val)
    (z : U32) : add x y ≠ .ok z := U32.traitAdd_no_success_on_overflow x y h z

theorem sub_spec (x y : U32) (h : y.val ≤ x.val) :
    sub x y ⦃ z => z.val = x.val - y.val ∧ z.bv = x.bv - y.bv ⦄ :=
  U32.traitSub_spec x y h

theorem sub_underflow (x y : U32) (h : x.val < y.val) :
    sub x y = .fail .integerOverflow := U32.traitSub_underflow x y h

theorem rem_spec (x y : U32) (h : y.val ≠ 0) :
    rem x y ⦃ z => z.val = x.val % y.val ⦄ := U32.traitRem_spec x y h

theorem rem_zero (x y : U32) (h : y.val = 0) :
    rem x y = .fail .divisionByZero := U32.traitRem_zero x y h

theorem not_spec (x : U32) :
    scalar_trait_ops.not x ⦃ z => z.bv = ~~~x.bv ⦄ := U32.traitNot_spec x

theorem and_spec (x y : U32) :
    scalar_trait_ops.and x y ⦃ z => z.bv = x.bv &&& y.bv ⦄ := U32.traitAnd_spec x y

theorem or_spec (x y : U32) :
    scalar_trait_ops.or x y ⦃ z => z.bv = x.bv ||| y.bv ⦄ := U32.traitOr_spec x y

theorem xor_spec (x y : U32) :
    scalar_trait_ops.xor x y ⦃ z => z.bv = x.bv ^^^ y.bv ⦄ := U32.traitXor_spec x y

theorem shl_spec (x : U32) (n : Usize) (h : n.val < 32) :
    shl x n ⦃ z => z.val = (x.val <<< n.val) % U32.size ∧ z.bv = x.bv <<< n.val ⦄ :=
  U32.traitShl_spec x n h

theorem shr_spec (x : U32) (n : Usize) (h : n.val < 32) :
    shr x n ⦃ z => z.val = x.val >>> n.val ∧ z.bv = x.bv >>> n.val ⦄ :=
  U32.traitShr_spec x n h

theorem shl_overflow (x : U32) (n : Usize) (h : 32 ≤ n.val) :
    shl x n = .fail .integerOverflow := U32.traitShl_overflow x n h

theorem shr_overflow (x : U32) (n : Usize) (h : 32 ≤ n.val) :
    shr x n = .fail .integerOverflow := U32.traitShr_overflow x n h

#print axioms add_spec
#print axioms add_no_success_on_overflow
#print axioms sub_spec
#print axioms sub_underflow
#print axioms rem_spec
#print axioms rem_zero
#print axioms not_spec
#print axioms and_spec
#print axioms or_spec
#print axioms xor_spec
#print axioms shl_spec
#print axioms shr_spec
#print axioms shl_overflow
#print axioms shr_overflow
#print axioms U32.traitAdd_spec
#print axioms U32.traitAdd_no_success_on_overflow
#print axioms U32.traitSub_spec
#print axioms U32.traitSub_underflow
#print axioms U32.traitRem_spec
#print axioms U32.traitRem_zero
#print axioms U32.traitNot_spec
#print axioms U32.traitAnd_spec
#print axioms U32.traitOr_spec
#print axioms U32.traitXor_spec
#print axioms U32.traitShl_spec
#print axioms U32.traitShr_spec
#print axioms U32.traitShl_overflow
#print axioms U32.traitShr_overflow
end scalar_trait_ops.tests
