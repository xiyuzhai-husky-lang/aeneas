module
public import Aeneas.Std.Core.Iter
public section

namespace Aeneas.Std
open Result

/-- Native Enumerate::next_back reads the remaining length after consuming the
back item. Only front consumption changes count; the inner updated iterator is
retained even when it returns None. Checked usize addition matches this MIR. -/
@[expose, rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Clause0_Item)>}::next_back"]
def core.iter.adapters.enumerate.DoubleEndedIteratorEnumerate.next_back
    {I Item : Type}
    (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (self : core.iter.adapters.enumerate.Enumerate I) :
    Result (Option (Usize × Item) × core.iter.adapters.enumerate.Enumerate I) := do
  let (item, iter) ← double.next_back self.iter
  match item with
  | none => ok (none, {self with iter})
  | some item => do
    let len ← exact.len iter
    let index ← self.count + len
    ok (some (index, item), {self with iter})

/-- The native rfold override decrements its private counter before calling the
user closure. The updated closure is passed to the next inner rfold callback. -/
@[expose]
def core.iter.adapters.enumerate.rfoldCall {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (state : Usize × F) (args : Acc × Item) : Result (Acc × (Usize × F)) := do
  let count ← state.1 - 1#usize
  let (acc, closure) ← fn.call_mut state.2 (args.1, (count, args.2))
  ok (acc, (count, closure))

@[expose]
def core.iter.adapters.enumerate.rfoldFnMut {Item Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc) :
    core.ops.function.FnMut (Usize × F) (Acc × Item) Acc := {
  FnOnceInst := {call_once := fun state args => do
    let (acc, _) ← core.iter.adapters.enumerate.rfoldCall fn state args
    ok acc}
  call_mut := core.iter.adapters.enumerate.rfoldCall fn
}

/-- Preserve Enumerate's actual rfold override and the inner iterator's own
rfold dispatch. Native order is len, checked addition, then delegated fold. -/
@[expose, rust_fun
  "core::iter::adapters::enumerate::{core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Clause0_Item)>}::rfold"]
def core.iter.adapters.enumerate.DoubleEndedIteratorEnumerate.rfold
    {I Item Acc F : Type}
    (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (self : core.iter.adapters.enumerate.Enumerate I) (init : Acc) (closure : F) : Result Acc := do
  let len ← exact.len self.iter
  let count ← self.count + len
  double.rfold (core.iter.adapters.enumerate.rfoldFnMut fn) self.iter init (count, closure)

@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::iter::adapters::enumerate::Enumerate<@I>, (usize, @Clause0_Clause0_Item)>"]
impl_def core.iter.adapters.enumerate.DoubleEndedIteratorEnumerate {I Item : Type}
    (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item) :
    core.iter.traits.double_ended.DoubleEndedIterator (core.iter.adapters.enumerate.Enumerate I) (Usize × Item) := {
  iteratorInst := core.iter.traits.iterator.IteratorEnumerate exact.iteratorInst
  next_back := core.iter.adapters.enumerate.DoubleEndedIteratorEnumerate.next_back exact double
  rfold := core.iter.adapters.enumerate.DoubleEndedIteratorEnumerate.rfold exact double
}

namespace core.iter.adapters.enumerate
variable {I Item : Type}

theorem next_back_none (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (self : Enumerate I) (iter : I) (next : double.next_back self.iter = ok (none, iter)) :
    DoubleEndedIteratorEnumerate.next_back exact double self = ok (none, {self with iter}) := by
  simp [DoubleEndedIteratorEnumerate.next_back, next]

theorem next_back_some (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (self : Enumerate I) (iter : I) (item : Item) (len index : Usize)
    (next : double.next_back self.iter = ok (some item, iter))
    (length : exact.len iter = ok len) (add : (self.count + len : Result Usize) = ok index) :
    DoubleEndedIteratorEnumerate.next_back exact double self = ok (some (index, item), {self with iter}) := by
  simp [DoubleEndedIteratorEnumerate.next_back, next, length, add]

theorem next_back_fail (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (self : Enumerate I) (error : Error) (next : double.next_back self.iter = fail error) :
    DoubleEndedIteratorEnumerate.next_back exact double self = fail error := by
  simp [DoubleEndedIteratorEnumerate.next_back, next]

theorem next_back_div (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (self : Enumerate I) (next : double.next_back self.iter = div) :
    DoubleEndedIteratorEnumerate.next_back exact double self = div := by
  simp [DoubleEndedIteratorEnumerate.next_back, next]

theorem rfoldCall_state {Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (state : Usize × F) (args : Acc × Item) (count : Usize) (acc : Acc) (closure : F)
    (subtract : (state.1 - 1#usize : Result Usize) = ok count)
    (called : fn.call_mut state.2 (args.1, (count, args.2)) = ok (acc, closure)) :
    rfoldCall fn state args = ok (acc, (count, closure)) := by
  simp [rfoldCall, subtract, called]

theorem rfoldCall_fail {Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (state : Usize × F) (args : Acc × Item) (count : Usize) (error : Error)
    (subtract : (state.1 - 1#usize : Result Usize) = ok count)
    (called : fn.call_mut state.2 (args.1, (count, args.2)) = fail error) :
    rfoldCall fn state args = fail error := by
  simp [rfoldCall, subtract, called]

theorem rfoldCall_div {Acc F : Type}
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (state : Usize × F) (args : Acc × Item) (count : Usize)
    (subtract : (state.1 - 1#usize : Result Usize) = ok count)
    (called : fn.call_mut state.2 (args.1, (count, args.2)) = div) :
    rfoldCall fn state args = div := by
  simp [rfoldCall, subtract, called]

theorem rfold_delegates {Acc F : Type}
    (exact : core.iter.traits.exact_size.ExactSizeIterator I Item)
    (double : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fn : core.ops.function.FnMut F (Acc × (Usize × Item)) Acc)
    (self : Enumerate I) (init : Acc) (closure : F) (len count : Usize)
    (length : exact.len self.iter = ok len) (add : (self.count + len : Result Usize) = ok count) :
    DoubleEndedIteratorEnumerate.rfold exact double fn self init closure =
      double.rfold (rfoldFnMut fn) self.iter init (count, closure) := by
  simp [DoubleEndedIteratorEnumerate.rfold, length, add]
end core.iter.adapters.enumerate
end Aeneas.Std
