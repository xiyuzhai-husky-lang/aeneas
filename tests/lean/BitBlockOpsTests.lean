module
public import BitBlockOps
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.WP
namespace bit_block_ops.tests

theorem count_ones_spec (x : U32) :
    ∃ n, count_ones x = .ok n ∧ n.val = x.ones ∧ n.val ≤ 32 :=
  U32.countOnes_spec x

theorem hash_dispatch {H : Type} (inst : core.hash.Hasher H) (x : U32) (state : H) :
    hash inst x state = inst.write_u32 state x := rfl

theorem hash_spec {H : Type} (inst : core.hash.Hasher H) (x : U32) (state out : H)
    (h : inst.write_u32 state x = .ok out) : hash inst x state = .ok out := h

theorem override_spec (x : U32) (state : OverrideHasher) (h : state.calls.val < U32.max) :
    ∃ out, hash OverrideHasher.Insts.CoreHashHasher x state = .ok out ∧
      out.seen = x ∧ out.calls.val = state.calls.val + 1 := by
  obtain ⟨n, hn, hval⟩ := WP.spec_imp_exists (U32.add_spec (x := state.calls) (y := 1#u32) (by scalar_tac))
  simp only [hash, core.hash.hashU32,
    OverrideHasher.Insts.CoreHashHasher.write_u32, hn, bind_ok]
  exact ⟨_, rfl, rfl, by simpa using hval⟩

#print axioms U32.ones_le
#print axioms U32.ones_zero
#print axioms U32.countOnes_spec
#print axioms Aeneas.Std.core.hash.hashU32_dispatch
#print axioms Aeneas.Std.core.hash.hashU32_spec
#print axioms count_ones_spec
#print axioms hash_dispatch
#print axioms hash_spec
#print axioms override_spec
end bit_block_ops.tests
