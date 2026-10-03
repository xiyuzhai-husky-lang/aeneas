module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result
public import Aeneas.Std.String
public section

namespace Aeneas.Std

open Result

/-- Returns the contained `some` value. The message is ignored: on `none`, this
    fails with `Error.panic`, which is the same behavior as `unwrap`. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::expect"]
def core.option.Option.expect {T : Type} (x : Option T) (_msg: Str) : Result T :=
  Result.ofOption x Error.panic

attribute [agrind =] Option.isSome_none Option.isSome_some

theorem core.option.Option.expect.spec {T : Type} (x : Option T) (msg: Str) (h : x.isSome) :
  expect x msg ⦃ v => x = some v ⦄ := by
  simp only [expect, Result.ofOption]; grind

@[expose, rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T E : Type} (x : Option T) (e : E) :
  Result (core.result.Result T E) :=
  match x with
  | some value => ok (.Ok value)
  | none => ok (.Err e)

@[simp]
theorem core.option.Option.ok_or_some {T E : Type} (value : T) (error : E) :
  core.option.Option.ok_or (some value) error = ok (.Ok value) := rfl

@[simp]
theorem core.option.Option.ok_or_none {T E : Type} (error : E) :
  core.option.Option.ok_or (none : Option T) error = ok (.Err error) := rfl


/-- Native lazy conversion: `some` does not call the closure; `none` calls it
once. Callback failure or divergence propagates through the ordinary Result bind. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::ok_or_else"]
def core.option.Option.ok_or_else
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F Unit E)
    (self : Option T) (f : F) : Result (core.result.Result T E) :=
  match self with
  | some value => ok (.Ok value)
  | none => do
      let error ← fnOnce.call_once f ()
      ok (.Err error)

@[simp]
theorem core.option.Option.ok_or_else_some
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F Unit E)
    (value : T) (f : F) :
    core.option.Option.ok_or_else fnOnce (some value) f = ok (.Ok value) := rfl

@[simp]
theorem core.option.Option.ok_or_else_none
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F Unit E) (f : F) :
    core.option.Option.ok_or_else fnOnce (none : Option T) f = (do
      let error ← fnOnce.call_once f ()
      ok (.Err error)) := rfl

/-- Successful lazy conversion observes exactly the single callback result. -/
theorem core.option.Option.ok_or_else_none_exact
    {T E F : Type} (fnOnce : core.ops.function.FnOnce F Unit E) (f : F) (error : E) :
    core.option.Option.ok_or_else fnOnce (none : Option T) f = ok (.Err error) ↔
      fnOnce.call_once f () = ok error := by
  simp only [ok_or_else]
  cases fnOnce.call_once f () <;> simp

/-- Native `is_some_and` consumes its closure exactly once for `some`, and
never calls it for `none`; the callback Result is returned unchanged. -/
@[expose, rust_fun "core::option::{core::option::Option<@T>}::is_some_and"]
def core.option.Option.is_some_and {T F : Type}
    (fn : core.ops.function.FnOnce F T Bool) (self : Option T) (f : F) : Result Bool :=
  match self with
  | none => ok false
  | some value => fn.call_once f value

@[simp] theorem core.option.Option.is_some_and_none {T F : Type}
    (fn : core.ops.function.FnOnce F T Bool) (f : F) :
    core.option.Option.is_some_and fn none f = ok false := rfl

@[simp] theorem core.option.Option.is_some_and_some {T F : Type}
    (fn : core.ops.function.FnOnce F T Bool) (value : T) (f : F) :
    core.option.Option.is_some_and fn (some value) f = fn.call_once f value := rfl

namespace core.option.Option
/-- The mutable-reference instantiation of native `Option::expect`. It returns
exactly the selected value and reconstructs `Some` when its borrow is returned. -/
@[expose]
def expect_mut {T : Type} (x : Option T) (_msg : Str) :
    Result (T × (T → Option T)) :=
  match x with
  | some value => ok (value, some)
  | none => fail .panic

@[simp] theorem expect_mut_some {T : Type} (value : T) (msg : Str) :
    expect_mut (some value) msg = ok (value, some) := rfl
@[simp] theorem expect_mut_none {T : Type} (msg : Str) :
    expect_mut (none : Option T) msg = fail .panic := rfl

theorem expect_mut_exact {T : Type} (x : Option T) (msg : Str) (value : T)
    (back : T → Option T) :
    expect_mut x msg = ok (value, back) ↔ x = some value ∧ back = some := by
  cases x <;> simp [expect_mut, eq_comm]
end core.option.Option

/-- Native Option equality calls the supplied equality exactly once for two
present values, and never calls it for differing variants or two absent values. -/
@[expose, rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (inst : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left, right with
  | some a, some b => inst.eq a b
  | none, none => ok true
  | _, _ => ok false

namespace core.option.Option.Insts.CoreCmpPartialEqOption
@[simp] theorem eq_some_some {T : Type} (inst : core.cmp.PartialEq T T) (a b : T) :
    eq inst (some a) (some b) = inst.eq a b := rfl
@[simp] theorem eq_none_none {T : Type} (inst : core.cmp.PartialEq T T) :
    eq inst none none = ok true := rfl
@[simp] theorem eq_some_none {T : Type} (inst : core.cmp.PartialEq T T) (a : T) :
    eq inst (some a) none = ok false := rfl
@[simp] theorem eq_none_some {T : Type} (inst : core.cmp.PartialEq T T) (a : T) :
    eq inst none (some a) = ok false := rfl
end core.option.Option.Insts.CoreCmpPartialEqOption

end Aeneas.Std
