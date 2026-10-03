module
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Core.Result

public section

namespace Aeneas.Std

open Result

/-- Pure model of `Result::map_err`: leaves `Ok` untouched and maps the payload
    of `Err` through `fnOnce`. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)

@[simp]
theorem core.result.Result.map_err_ok
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) (value : T) (f : O) :
  core.result.Result.map_err fnOnce (.Ok value) f =
    ok (core.result.Result.Ok value : core.result.Result T F) := rfl

@[simp]
theorem core.result.Result.map_err_err
  {T E F O : Type} (fnOnce : core.ops.function.FnOnce O E F) (error : E) (f : O) :
  core.result.Result.map_err fnOnce
      (core.result.Result.Err error : core.result.Result T E) f = (do
    let mapped ← fnOnce.call_once f error
    ok (core.result.Result.Err mapped : core.result.Result T F)) := rfl


/-- Exact native discriminant test; neither payload is inspected. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T E : Type} (self : core.result.Result T E) :
    Std.Result Bool :=
  match self with
  | .Ok _ => ok false
  | .Err _ => ok true

@[simp] theorem core.result.Result.is_err_ok {T E : Type} (value : T) :
    core.result.Result.is_err (.Ok value : core.result.Result T E) = ok false := rfl

@[simp] theorem core.result.Result.is_err_err {T E : Type} (error : E) :
    core.result.Result.is_err (.Err error : core.result.Result T E) = ok true := rfl

/-- Native `and_then`: an `Ok` calls its owned closure exactly once, while an
`Err` returns the original error. The callback Result is returned unchanged. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::and_then"]
def core.result.Result.and_then
    {T E U F : Type} (fnOnce : core.ops.function.FnOnce F T (core.result.Result U E))
    (self : core.result.Result T E) (f : F) : Std.Result (core.result.Result U E) :=
  match self with
  | .Ok value => fnOnce.call_once f value
  | .Err error => ok (.Err error)

@[simp]
theorem core.result.Result.and_then_ok
    {T E U F : Type} (fnOnce : core.ops.function.FnOnce F T (core.result.Result U E))
    (value : T) (f : F) :
    core.result.Result.and_then fnOnce (.Ok value) f = fnOnce.call_once f value := rfl

@[simp]
theorem core.result.Result.and_then_err
    {T E U F : Type} (fnOnce : core.ops.function.FnOnce F T (core.result.Result U E))
    (error : E) (f : F) :
    core.result.Result.and_then fnOnce (.Err error : core.result.Result T E) f =
      ok (.Err error) := rfl

/-- Applied native `and_then` for a once-only closure with one mutable capture.
The successful callback returns its complete native closure state; an Err does
not invoke the callback and gives back the unchanged captured state. -/
@[expose]
def core.result.Result.and_then_mut_capture {T E U F : Type}
    (fn : core.ops.function.FnOnce F T (core.result.Result U E × F))
    (self : core.result.Result T E) (f : F) : Std.Result (core.result.Result U E × F) :=
  match self with
  | .Ok value => fn.call_once f value
  | .Err error => ok (.Err error, f)

@[simp] theorem core.result.Result.and_then_mut_capture_ok {T E U F : Type}
    (fn : core.ops.function.FnOnce F T (core.result.Result U E × F)) (value : T) (f : F) :
    core.result.Result.and_then_mut_capture fn (.Ok value) f = fn.call_once f value := rfl

@[simp] theorem core.result.Result.and_then_mut_capture_err {T E U F : Type}
    (fn : core.ops.function.FnOnce F T (core.result.Result U E × F)) (error : E) (f : F) :
    core.result.Result.and_then_mut_capture fn (.Err error : core.result.Result T E) f =
      ok (.Err error, f) := rfl

/-- Keep the successful payload and discard only an error, as native `Result::ok`. -/
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type} (self : core.result.Result T E) : Std.Result (Option T) :=
  match self with
  | .Ok value => Std.Result.ok (some value)
  | .Err _ => Std.Result.ok none

@[simp] theorem core.result.Result.ok_ok {T E : Type} (value : T) :
    core.result.Result.ok (.Ok value : core.result.Result T E) = Std.Result.ok (some value) := rfl

@[simp] theorem core.result.Result.ok_err {T E : Type} (error : E) :
    core.result.Result.ok (.Err error : core.result.Result T E) = Std.Result.ok none := rfl

end Aeneas.Std
