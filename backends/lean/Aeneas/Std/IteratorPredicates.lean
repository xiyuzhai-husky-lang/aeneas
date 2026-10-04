module
public import Aeneas.Std.VecSupport
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std
open Result WP

/-- Generic short-circuit any consumes the matching item before returning.
    FnMut state evolves between calls; infinite false streams may diverge. -/
@[expose, trait_default, rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default {I T F : Type}
    (iter : core.iter.traits.iterator.Iterator I T) (call : core.ops.function.FnMut F T Bool)
    (self : I) (f : F) : Result (Bool × I) := do
  let output ← iter.next self
  match output.1 with
  | none => .ok (false, output.2)
  | some x =>
    let tested ← call.call_mut f x
    if tested.1 then .ok (true, output.2)
    else core.iter.traits.iterator.Iterator.any.default iter call output.2 tested.2
partial_fixpoint

/-- Generic short-circuit all consumes the first false item before returning.
    Failure/divergence from next or the predicate is propagated unchanged. -/
@[expose, trait_default, rust_fun "core::iter::traits::iterator::Iterator::all"]
def core.iter.traits.iterator.Iterator.all.default {I T F : Type}
    (iter : core.iter.traits.iterator.Iterator I T) (call : core.ops.function.FnMut F T Bool)
    (self : I) (f : F) : Result (Bool × I) := do
  let output ← iter.next self
  match output.1 with
  | none => .ok (true, output.2)
  | some x =>
    let tested ← call.call_mut f x
    if tested.1 then core.iter.traits.iterator.Iterator.all.default iter call output.2 tested.2
    else .ok (false, output.2)
partial_fixpoint

@[expose, rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.IteratorSliceIter.any {T F : Type}
    (call : core.ops.function.FnMut F T Bool) (self : core.slice.iter.Iter T) (f : F) :
    Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.any.default (core.iter.traits.iterator.IteratorSliceIter T) call self f

@[expose, rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.IteratorSliceIter.all {T F : Type}
    (call : core.ops.function.FnMut F T Bool) (self : core.slice.iter.Iter T) (f : F) :
    Result (Bool × core.slice.iter.Iter T) :=
  core.iter.traits.iterator.Iterator.all.default (core.iter.traits.iterator.IteratorSliceIter T) call self f

/-- Finite concrete iteration with an actual stateless predicate trace proves
    termination and the list-any result; enclosing any success is not assumed. -/
theorem core.iter.traits.iterator.Iterator.any.finite {I T F : Type}
    (iter : core.iter.traits.iterator.Iterator I T) (call : core.ops.function.FnMut F T Bool)
    {s : I} {xs : List T} (trace : IteratorTrace iter s xs) (f : F) (p : T → Bool)
    (calls : ∀ x ∈ xs, call.call_mut f x = .ok (p x, f)) :
    ∃ next, core.iter.traits.iterator.Iterator.any.default iter call s f = .ok (xs.any p, next) := by
  induction trace with
  | @done s next he =>
    refine ⟨next, ?_⟩
    rw [core.iter.traits.iterator.Iterator.any.default]
    simp only [he, bind_tc_ok, List.any_nil]
  | @step s next x xs he trace ih =>
    have test := calls x (List.mem_cons_self ..)
    have tailCalls : ∀ y ∈ xs, call.call_mut f y = .ok (p y, f) :=
      fun y hy => calls y (List.mem_cons_of_mem x hy)
    cases value : p x with
    | false =>
      obtain ⟨finish, tail⟩ := ih tailCalls
      refine ⟨finish, ?_⟩
      rw [core.iter.traits.iterator.Iterator.any.default]
      simp only [he, bind_tc_ok, test, value, Bool.false_eq_true, if_false]
      simpa only [List.any_cons, value, Bool.false_or] using tail
    | true =>
      refine ⟨next, ?_⟩
      rw [core.iter.traits.iterator.Iterator.any.default]
      simp only [he, bind_tc_ok, test, value, if_true, List.any_cons, Bool.true_or]

/-- The analogous finite trace proves all's result, including the empty case. -/
theorem core.iter.traits.iterator.Iterator.all.finite {I T F : Type}
    (iter : core.iter.traits.iterator.Iterator I T) (call : core.ops.function.FnMut F T Bool)
    {s : I} {xs : List T} (trace : IteratorTrace iter s xs) (f : F) (p : T → Bool)
    (calls : ∀ x ∈ xs, call.call_mut f x = .ok (p x, f)) :
    ∃ next, core.iter.traits.iterator.Iterator.all.default iter call s f = .ok (xs.all p, next) := by
  induction trace with
  | @done s next he =>
    refine ⟨next, ?_⟩
    rw [core.iter.traits.iterator.Iterator.all.default]
    simp only [he, bind_tc_ok, List.all_nil]
  | @step s next x xs he trace ih =>
    have test := calls x (List.mem_cons_self ..)
    have tailCalls : ∀ y ∈ xs, call.call_mut f y = .ok (p y, f) :=
      fun y hy => calls y (List.mem_cons_of_mem x hy)
    cases value : p x with
    | false =>
      refine ⟨next, ?_⟩
      rw [core.iter.traits.iterator.Iterator.all.default]
      simp only [he, bind_tc_ok, test, value, Bool.false_eq_true, if_false, List.all_cons, Bool.false_and]
    | true =>
      obtain ⟨finish, tail⟩ := ih tailCalls
      refine ⟨finish, ?_⟩
      rw [core.iter.traits.iterator.Iterator.all.default]
      simp only [he, bind_tc_ok, test, value, if_true]
      simpa only [List.all_cons, value, Bool.true_and] using tail

/-- The front index retains consumed front items; consuming from the back
    shortens the stored slice. This models both endpoints without changing the
    existing forward-iterator representation or returning consumed items twice. -/
@[expose, rust_fun
  "core::slice::iter::{core::iter::traits::double_ended::DoubleEndedIterator<core::slice::iter::Iter<'a, @T>, &'_ @T>}::next_back"]
def core.slice.iter.IteratorSliceIter.next_back {T : Type} (self : core.slice.iter.Iter T) :
    Result (Option T × core.slice.iter.Iter T) :=
  if h : self.i < self.slice.val.length then
    let index := self.slice.val.length - 1
    let value := self.slice.val[index]'(by scalar_tac)
    let slice : Slice T := .from (self.slice.val.take index)
      ((List.length_take_le _ _).trans ((Nat.sub_le _ _).trans self.slice.property))
    .ok (some value, ⟨slice, self.i⟩)
  else .ok (none, self)

/-- No unread items means next_back succeeds with None and exact unchanged state. -/
theorem core.slice.iter.IteratorSliceIter.next_back_empty {T : Type}
    (self : core.slice.iter.Iter T) (empty : self.slice.val.length ≤ self.i) :
    core.slice.iter.IteratorSliceIter.next_back self = .ok (none, self) := by
  simp only [core.slice.iter.IteratorSliceIter.next_back, dif_neg (Nat.not_lt.mpr empty)]

/-- A real back step returns the last unread item, preserves the front cursor,
    and removes exactly the final physical item from the iterator's slice. -/
theorem core.slice.iter.IteratorSliceIter.next_back_nonempty {T : Type}
    (self : core.slice.iter.Iter T) (pending : self.i < self.slice.val.length) :
    ∃ x next, core.slice.iter.IteratorSliceIter.next_back self = .ok (some x, next) ∧
      x = self.slice.val[self.slice.val.length - 1]'(by scalar_tac) ∧ next.i = self.i ∧
      next.slice.val = self.slice.val.take (self.slice.val.length - 1) ∧
      next.slice.val.length = self.slice.val.length - 1 := by
  let slice : Slice T := .from (self.slice.val.take (self.slice.val.length - 1))
    ((List.length_take_le _ _).trans ((Nat.sub_le _ _).trans self.slice.property))
  refine ⟨self.slice.val[self.slice.val.length - 1]'(by scalar_tac), ⟨slice, self.i⟩, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [core.slice.iter.IteratorSliceIter.next_back, dif_pos pending, slice]
  · exact Slice.from_val _ _
  · rw [Slice.from_val, List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

end Aeneas.Std
