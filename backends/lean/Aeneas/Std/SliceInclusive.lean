module
public import Aeneas.Std.Slice
public section
@[expose] section
namespace Aeneas.Std
open Result core.ops.range

/-- Checked conversion used by native inclusive slice indexing. Exhausted ranges
start at the exclusive endpoint, and `end < len` prevents endpoint overflow.
This is a functional library model; native unsafe pointer internals remain outside
its correspondence claim, as for the existing slice-index models. -/
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range {T : Type}
    (r : RangeInclusive Usize) (s : Slice T) : Option (Range Usize) :=
  if h : r.end.val < s.val.length then
    let endpoint := Usize.ofNatCore (r.end.val + 1) (by have := s.property; scalar_tac)
    some ⟨if r.exhausted then endpoint else r.start,endpoint⟩
  else none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get {T : Type}
    (r : RangeInclusive Usize) (s : Slice T) : Result (Option (Slice T)) :=
  match core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range r s with
  | none => ok none
  | some bounds => core.slice.index.SliceIndexRangeUsizeSlice.get bounds s

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_mut {T : Type}
    (r : RangeInclusive Usize) (s : Slice T) : Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  match core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range r s with
  | none => ok (none,fun _ => s)
  | some bounds => core.slice.index.SliceIndexRangeUsizeSlice.get_mut bounds s

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_unchecked {T : Type} :
    RangeInclusive Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_unchecked_mut {T : Type} :
    RangeInclusive Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index {T : Type}
    (r : RangeInclusive Usize) (s : Slice T) : Result (Slice T) :=
  match core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range r s with
  | none => fail .panic
  | some bounds => core.slice.index.SliceIndexRangeUsizeSlice.index bounds s

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index_mut {T : Type}
    (r : RangeInclusive Usize) (s : Slice T) : Result (Slice T × (Slice T → Slice T)) :=
  match core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range r s with
  | none => fail .panic
  | some bounds => core.slice.index.SliceIndexRangeUsizeSlice.index_mut bounds s

@[reducible,rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeInclusive<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeInclusiveUsizeSlice (T : Type) :
    core.slice.index.SliceIndex (RangeInclusive Usize) (Slice T) (Slice T) where
  get := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index_mut

namespace SliceInclusiveModel

theorem index_exact {T : Type} (s : Slice T) (low high : Usize)
    (order : low.val ≤ high.val + 1) (inside : high.val < s.val.length) :
    ∃ output, core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index ⟨low,high,false⟩ s = ok output ∧
      output.val = s.val.slice low.val (high.val + 1) := by
  simp only [core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index,
    core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range,inside,dif_pos,Bool.false_eq_true,ite_false]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,UScalar.le_equiv,Usize.ofNatCore_val_eq,Slice.length]
  simp only [order,show high.val + 1 ≤ s.val.length by omega,and_self,true_and,ite_true]
  exact ⟨_,rfl,Slice.from_val _ _⟩

theorem index_exhausted {T : Type} (s : Slice T) (low high : Usize)
    (inside : high.val < s.val.length) :
    ∃ output, core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index ⟨low,high,true⟩ s = ok output ∧ output.val = [] := by
  simp only [core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index,
    core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range,inside,dif_pos,ite_true]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,UScalar.le_equiv,Usize.ofNatCore_val_eq,Slice.length]
  simp only [Nat.le_refl,show high.val + 1 ≤ s.val.length by omega,and_self,true_and,ite_true]
  refine ⟨_,rfl,?_⟩
  simp only [Slice.from_val,List.slice]
  simp

theorem index_past_end {T : Type} (s : Slice T) (r : RangeInclusive Usize)
    (outside : s.val.length ≤ r.end.val) :
    core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index r s = fail .panic := by
  simp only [core.slice.index.SliceIndexRangeInclusiveUsizeSlice.index,
    core.slice.index.SliceIndexRangeInclusiveUsizeSlice.range,show ¬r.end.val < s.val.length by omega,dif_neg,↓reduceDIte]

#print axioms index_exact
#print axioms index_exhausted
#print axioms index_past_end
end SliceInclusiveModel
end Aeneas.Std
