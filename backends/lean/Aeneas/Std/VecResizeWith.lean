module
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Vec
public section

namespace Aeneas.Std
open Result

/-- Invoke the owned generator in order, carrying its mutable closure state.
The native implementation uses `repeat_with(f).take(n)` for this same sequence.
Allocation, destruction, and panic unwinding remain library-model boundaries. -/
def alloc.vec.Vec.generateWith {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) :
    (n : Nat) → F → Result ({ items : List T // items.length = n } × F)
  | 0, f => ok (⟨[], rfl⟩, f)
  | n + 1, f => do
    let (item, f') ← fn.call_mut f ()
    let (items, f'') ← generateWith fn n f'
    ok (⟨item :: items.val, by simp [items.property]⟩, f'')

@[expose, rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::resize_with"
  (keepParams := [true, false, true])]
def alloc.vec.Vec.resize_with {T F : Type}
    (fn : core.ops.function.FnMut F Unit T)
    (v : alloc.vec.Vec T) (newLen : Usize) (f : F) : Result (alloc.vec.Vec T) := do
  if h : newLen.val ≤ v.val.length then
    ok (.from (v.val.take newLen.val) (by
      have hn : newLen.val ≤ Usize.max := by scalar_tac
      simp only [List.length_take]
      omega))
  else
    let (items, _) ← alloc.vec.Vec.generateWith fn (newLen.val - v.val.length) f
    ok (.from (v.val ++ items.val) (by
      have hn : newLen.val ≤ Usize.max := by scalar_tac
      simp only [List.length_append, items.property]
      omega))

theorem alloc.vec.Vec.generateWith_constant {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) (value : T)
    (hfn : ∀ f, fn.call_mut f () = ok (value, f)) (n : Nat) (f : F) :
    generateWith fn n f = ok (⟨List.replicate n value, by simp⟩, f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [generateWith, hfn, ih, List.replicate_succ]

theorem alloc.vec.Vec.resize_with_shrink {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) (v : alloc.vec.Vec T)
    (newLen : Usize) (f : F) (h : newLen.val ≤ v.val.length) :
    ∃ result, resize_with fn v newLen f = ok result ∧
      result.val = v.val.take newLen.val := by
  simp [resize_with, h]

theorem alloc.vec.Vec.resize_with_constant {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) (value : T)
    (hfn : ∀ f, fn.call_mut f () = ok (value, f))
    (v : alloc.vec.Vec T) (newLen : Usize) (f : F) :
    ∃ result, resize_with fn v newLen f = ok result ∧
      result.val = v.val.take newLen.val ++
        List.replicate (newLen.val - v.val.length) value := by
  by_cases h : newLen.val ≤ v.val.length
  · simp [resize_with, h, Nat.sub_eq_zero_of_le h]
  · have hle : v.val.length ≤ newLen.val := by omega
    simp [resize_with, h, generateWith_constant fn value hfn,
      List.take_of_length_le hle]

theorem alloc.vec.Vec.resize_with_grow_fail {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) (v : alloc.vec.Vec T)
    (newLen : Usize) (f : F) (err : Error)
    (h : v.val.length < newLen.val)
    (hgen : generateWith fn (newLen.val - v.val.length) f = fail err) :
    resize_with fn v newLen f = fail err := by
  simp [resize_with, Nat.not_le_of_lt h, hgen]

theorem alloc.vec.Vec.resize_with_grow_div {T F : Type}
    (fn : core.ops.function.FnMut F Unit T) (v : alloc.vec.Vec T)
    (newLen : Usize) (f : F) (h : v.val.length < newLen.val)
    (hgen : generateWith fn (newLen.val - v.val.length) f = .div) :
    resize_with fn v newLen f = .div := by
  simp [resize_with, Nat.not_le_of_lt h, hgen]

end Aeneas.Std
