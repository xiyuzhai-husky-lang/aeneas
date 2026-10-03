module
public import Aeneas.Std.Scalar

@[expose] public section
namespace Aeneas.Std

/-- Number of set bits, counted over all 32 bit positions. -/
def U32.ones (x : U32) : Nat :=
  (List.range 32).countP (fun i => x.bv.getLsbD i)

theorem U32.ones_le (x : U32) : x.ones ≤ 32 := by
  exact (List.countP_le_length).trans (by simp)

@[rust_fun "core::num::{u32}::count_ones"]
def core.num.U32.countOnes (x : U32) : Result U32 :=
  .ok (U32.ofNatCore x.ones (by have := x.ones_le; scalar_tac))

theorem U32.countOnes_spec (x : U32) :
    ∃ n, core.num.U32.countOnes x = .ok n ∧ n.val = x.ones ∧ n.val ≤ 32 := by
  unfold core.num.U32.countOnes
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp only [U32.ofNatCore_val_eq]
  · exact x.ones_le

theorem U32.ones_zero : U32.ones 0#u32 = 0 := by
  simp [U32.ones]

end Aeneas.Std
