module
public import Aeneas.Std.Float
public import Lean.Elab.Tactic.Omega

public section
namespace Aeneas.Std.BinaryFloat

/-- Nearest-even rounding selects the floor or its successor. -/
theorem roundQuotient_bounds (n d : Nat) :
    n / d ≤ roundQuotient n d ∧ roundQuotient n d ≤ n / d + 1 := by
  simp only [roundQuotient]
  split <;> omega

/-- The exact result differs from the selected integer by at most half a unit.
The inequalities avoid real arithmetic and cover arbitrarily large integers. -/
theorem roundQuotient_half (n d : Nat) (hd : 0 < d) :
    2 * n ≤ 2 * (roundQuotient n d * d) + d ∧
    2 * (roundQuotient n d * d) ≤ 2 * n + d := by
  have hr := Nat.mod_lt n hd
  have hq := Nat.mod_add_div n d
  rw [Nat.mul_comm d (n / d)] at hq
  simp only [roundQuotient]
  split <;> rename_i h
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    omega

/-- At a tie the selected integer is even, including subnormal rounding. -/
theorem roundQuotient_tie_even (n d : Nat) (h : 2 * (n % d) = d) :
    roundQuotient n d % 2 = 0 := by
  have hp := Nat.mod_lt (n / d) (by decide : 0 < 2)
  simp only [roundQuotient]
  split <;> rename_i hc
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    omega
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    omega

@[simp] theorem magnitude_neg (x : BinaryFloat e f) :
    (neg x).magnitude = x.magnitude := by
  have h : e + f ≤ 1 + e + f := by omega
  change ((x.bits ^^^ BitVec.ofNat _ (2 ^ (e + f))).toNat % 2 ^ (e + f)) = _
  rw [← BitVec.toNat_setWidth, BitVec.setWidth_xor,
    BitVec.setWidth_ofNat_of_le h]
  simp [magnitude, BitVec.ofNat, BitVec.toNat_setWidth]

@[simp] theorem isNaN_neg (x : BinaryFloat e f) : (neg x).isNaN = x.isNaN := by
  simp [isNaN]

theorem ObsEq.refl (x : BinaryFloat e f) : ObsEq x x := Or.inl rfl
theorem ObsEq.symm {x y : BinaryFloat e f} (h : ObsEq x y) : ObsEq y x := by
  rcases h with h | ⟨hx, hy⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hy, hx⟩
theorem ObsEq.trans {x y z : BinaryFloat e f} (hxy : ObsEq x y) (hyz : ObsEq y z) :
    ObsEq x z := by
  rcases hxy with rfl | ⟨hx, hy⟩
  · exact hyz
  rcases hyz with rfl | ⟨hy, hz⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hz⟩

theorem ObsEq.eq_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : eq x y = eq x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [eq, hy, hy']
  · simp [eq, hx, hx']

theorem ObsEq.lt_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : lt x y = lt x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [lt, hy, hy']
  · simp [lt, hx, hx']

theorem ObsEq.neg_congr {x y : BinaryFloat e f} (h : ObsEq x y) :
    ObsEq (neg x) (neg y) := by
  rcases h with rfl | ⟨hx, hy⟩
  · exact .refl _
  · exact Or.inr ⟨by simpa, by simpa⟩

-- Every arithmetic operation is insensitive to the NaN representative chosen.
theorem ObsEq.add_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : add x y = add x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [add, hy, hy']
  · simp [add, hx, hx']

theorem ObsEq.mul_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : mul x y = mul x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [mul, hy, hy']
  · simp [mul, hx, hx']

theorem ObsEq.div_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : div x y = div x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [div, hy, hy']
  · simp [div, hx, hx']

theorem ObsEq.rem_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : rem x y = rem x' y' := by
  rcases hx with rfl | ⟨hx, hx'⟩
  · rcases hy with rfl | ⟨hy, hy'⟩
    · rfl
    · simp [rem, hy, hy']
  · simp [rem, hx, hx']

theorem ObsEq.sub_congr {x x' y y' : BinaryFloat e f}
    (hx : ObsEq x x') (hy : ObsEq y y') : sub x y = sub x' y' :=
  hx.add_congr hy.neg_congr
end Aeneas.Std.BinaryFloat
