module
public import VecOperations
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace vec_operations.tests

theorem rust_as_slice {T : Type} (v : alloc.vec.Vec T) :
    as_slice v = .ok v.slice := by
  simp [as_slice, alloc.vec.Vec.as_slice_eq_slice]

theorem rust_truncate {T : Type} (v : alloc.vec.Vec T) (n : Usize) :
    truncate v n ⦃ w => w.val = v.val.take n.val ∧
      w.length = min n.val v.length ⦄ :=
  alloc.vec.Vec.truncate_spec v n

theorem rust_remove {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (h : i.val < v.length) :
    remove v i ⦃ r => r.1 = v.val[i.val] ∧
      r.2.val = v.val.take i.val ++ v.val.drop (i.val + 1) ∧
      r.2.length = v.length - 1 ⦄ :=
  alloc.vec.Vec.remove_spec v i h

theorem rust_remove_out_of_bounds {T : Type} (v : alloc.vec.Vec T) (i : Usize)
    (h : v.length ≤ i.val) : remove v i = .fail .arrayOutOfBounds :=
  alloc.vec.Vec.remove_out_of_bounds v i h

theorem rust_pop_reconstruct {T : Type} (v : alloc.vec.Vec T) :
    pop v ⦃ r => r.2.val ++ r.1.toList = v.val ∧
      r.2.length = v.length - 1 ⦄ := by
  simp [pop, alloc.vec.Vec.pop, List.dropLast_eq_take]

theorem rust_clear {T : Type} (v : alloc.vec.Vec T) :
    clear v ⦃ w => w.val = [] ⦄ := alloc.vec.Vec.clear_spec v

theorem rust_is_empty {T : Type} (v : alloc.vec.Vec T) :
    is_empty v = .ok true ↔ v.val = [] := by
  simp [is_empty]

theorem rust_retain {T F : Type} (fnMut : core.ops.function.FnMut F T Bool)
    (v : alloc.vec.Vec T) (state : F) (p : T → Bool)
    (hcall : ∀ state x, x ∈ v.val → ∃ next, fnMut.call_mut state x = .ok (p x, next)) :
    retain fnMut v state ⦃ w => w.val = v.val.filter p ⦄ :=
  alloc.vec.Vec.retain_spec fnMut v state p hcall

theorem rust_dedup {T : Type} [DecidableEq T]
    (eqInst : core.cmp.PartialEq T T) (v : alloc.vec.Vec T)
    (hcall : ∀ x y, eqInst.eq x y = .ok (decide (x = y))) :
    dedup eqInst v ⦃ w =>
      (∀ x, x ∈ w.val ↔ x ∈ v.val) ∧ w.val.Sublist v.val ∧
      w.val.IsChain (· ≠ ·) ⦄ := alloc.vec.Vec.dedup_eq_spec eqInst v hcall

#print axioms rust_as_slice
#print axioms rust_truncate
#print axioms rust_remove
#print axioms rust_remove_out_of_bounds
#print axioms rust_pop_reconstruct
#print axioms rust_clear
#print axioms rust_is_empty
#print axioms rust_retain
#print axioms rust_dedup
#print axioms alloc.vec.Vec.as_slice_val
#print axioms alloc.vec.Vec.as_slice_eq_slice
#print axioms alloc.vec.Vec.truncate_spec
#print axioms alloc.vec.Vec.truncate_of_length_le
#print axioms alloc.vec.Vec.remove_spec
#print axioms alloc.vec.Vec.remove_out_of_bounds
#print axioms alloc.vec.Vec.pop_spec
#print axioms alloc.vec.Vec.pop_empty
#print axioms alloc.vec.Vec.clear_spec
#print axioms alloc.vec.Vec.is_empty_iff
#print axioms alloc.vec.Vec.retainList_filter
#print axioms alloc.vec.Vec.retain_spec
#print axioms alloc.vec.Vec.dedupFrom_destutter
#print axioms alloc.vec.Vec.dedup_spec
#print axioms alloc.vec.Vec.mem_destutterFrom_ne
#print axioms alloc.vec.Vec.mem_destutter_ne
#print axioms alloc.vec.Vec.dedup_eq_spec
end vec_operations.tests
