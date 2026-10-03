module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Array.Array
public import Aeneas.Std.StringDef
public section

namespace Aeneas.Std

@[reducible, expose, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

/-- Logical external-sink boundary for `Formatter::write_str`.

The native formatter stores formatting options and a mutable `dyn Write` sink;
`write_str` forwards directly to that sink. The natural-number tokens represent
opaque options and sink state, not output bytes. The supplied callback determines
all observable write results and state transitions, including rejection, panic,
and divergence. Clients using this boundary must relate their native sink to the
chosen callback; no global successful writer or allocator assumption is installed.

This carrier does not establish correctness of the remaining Debug helpers below,
whose TODO models remain outside that observation boundary. `write_fmt` models
literal pieces and default-options placeholders; its unsupported branch is a
model-coverage boundary, not native error semantics. -/
@[rust_type "core::fmt::Formatter"]
structure core.fmt.Formatter where
  options : Nat
  writerState : Nat
  writeStr : Nat → Str → Result (core.result.Result Unit core.fmt.Error × Nat)

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type u) where
  fmt : T → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

-- TODO: move?
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

@[step]
theorem core.result.Result.unwrap.step_spec
    {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E)
    (h : ∃ v, r = core.result.Result.Ok v) :
    core.result.Result.unwrap inst r
    ⦃ (result : T) => r = core.result.Result.Ok result ⦄ := by
  match r, h with
  | .Ok v, ⟨_, rfl⟩ =>
    simp [core.result.Result.unwrap, WP.spec_ok]

-- TODO: add pattern once we support partial monomorphization
def core.result.Result.unwrap.mut {T E : Type}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result (T × (T → core.result.Result T E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok x)
  | .Err _ => .fail .panic


/-- A native formatting argument retains the selected trait callback and its
captured value. Calling `format` invokes precisely that callback; it does not
replace it with an always-successful printer. -/
@[rust_type "core::fmt::rt::Argument"]
structure core.fmt.rt.Argument where
  format : core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

/-- The two native representations, with their contents retained. `encoded`
stores the original compiler template and ordered argument callbacks. -/
@[rust_type "core::fmt::Arguments"]
inductive core.fmt.Arguments where
  | literal : Str → core.fmt.Arguments
  | encoded : List U8 → List core.fmt.rt.Argument → core.fmt.Arguments

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"]
def core.fmt.Arguments.from_str (text : Str) : Result core.fmt.Arguments :=
  .ok (.literal text)

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::new"]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (template : Std.Array Std.U8 N) (args : Std.Array core.fmt.rt.Argument M) : Result core.fmt.Arguments :=
  .ok (.encoded template.val args.val)

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"]
def core.fmt.rt.Argument.new_debug
  {T : Type} (inst : core.fmt.Debug T) (value : T) : Result core.fmt.rt.Argument :=
  .ok ⟨inst.fmt value⟩

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_lower_hex"]
def core.fmt.rt.Argument.new_lower_hex
  {T : Type} (inst : core.fmt.LowerHex T) (value : T) :
  Result core.fmt.rt.Argument :=
  .ok ⟨inst.fmt value⟩

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (text : Str) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) := do
  let (outcome, state) ← fmt.writeStr fmt.writerState text
  .ok (outcome, { fmt with writerState := state })

/-- The native sink's ordinary result and updated state are returned unchanged.
In particular an `Err` may still carry an updated sink state. -/
theorem core.fmt.Formatter.write_str_return (fmt : core.fmt.Formatter) (text : Str)
    (outcome : core.result.Result Unit core.fmt.Error) (state : Nat)
    (write : fmt.writeStr fmt.writerState text = .ok (outcome, state)) :
    fmt.write_str text = .ok (outcome, { fmt with writerState := state }) := by
  simp [core.fmt.Formatter.write_str, write]

/-- Primitive failure is propagated; no successful write is substituted. -/
theorem core.fmt.Formatter.write_str_failure (fmt : core.fmt.Formatter) (text : Str)
    (error : Std.Error) (write : fmt.writeStr fmt.writerState text = .fail error) :
    fmt.write_str text = .fail error := by
  simp [core.fmt.Formatter.write_str, write]

/-- A divergent sink remains divergent. -/
theorem core.fmt.Formatter.write_str_divergence (fmt : core.fmt.Formatter) (text : Str)
    (write : fmt.writeStr fmt.writerState text = .div) :
    fmt.write_str text = .div := by
  simp [core.fmt.Formatter.write_str, write]

/-- Logical token for `FormattingOptions::new()` (no flags, width, or precision).
Other option tokens are outside the default-formatting fragment below. -/
@[expose] def core.fmt.defaultOptions : Nat := 0

/-- Construct the exact literal slice, checking the native size boundary. -/
@[expose] def core.fmt.literalSlice (bytes : List U8) : Result Str :=
  if h : bytes.length ≤ Usize.max then .ok (.from bytes h)
  else .fail .maximumSizeExceeded

/-- Execute the native default/literal bytecode fragment in source order.
Short and u16-length literals and 0xC0 default placeholders are modeled. Custom
format options are not covered: `.undef` there denotes missing model coverage,
not an assertion that native formatting fails. Malformed unsafe templates are
also outside correspondence. Ordinary sink/argument Err, failure and divergence
are propagated. One fuel unit accounts for each consumed opcode byte. -/
@[expose] def core.fmt.writeTemplate : Nat → List U8 → List core.fmt.rt.Argument → Nat →
    core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)
  | 0, _, _, _, _ => .fail .undef
  | fuel + 1, template, args, index, fmt => do
      match template with
      | [] => .fail .undef
      | opcode :: rest =>
          if opcode.val = 0 then .ok (.Ok (), fmt)
          else if opcode.val = 192 then
            match args[index]? with
            | none => .fail .undef
            | some argument =>
                let (outcome, after) ← argument.format {fmt with options := defaultOptions}
                let updated := {fmt with writerState := after.writerState}
                match outcome with
                | .Err error => .ok (.Err error, updated)
                | .Ok () => writeTemplate fuel rest args (index + 1) updated
          else
            let (length, contents) ←
              if opcode.val < 128 then .ok (opcode.val, rest)
              else if opcode.val = 128 then
                match rest with
                | lo :: hi :: tail => .ok (lo.val + 256 * hi.val, tail)
                | _ => .fail .undef
              else .fail .undef
            if length > contents.length then .fail .undef
            else
              let text ← literalSlice (contents.take length)
              let (outcome, updated) ← fmt.write_str text
              match outcome with
              | .Err error => .ok (.Err error, updated)
              | .Ok () => writeTemplate fuel (contents.drop length) args index updated

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt
  (fmt : core.fmt.Formatter) (args : core.fmt.Arguments) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  match args with
  | .literal text => fmt.write_str text
  | .encoded template arguments => core.fmt.writeTemplate (template.length + 1) template arguments 0 fmt

@[simp] theorem core.fmt.Formatter.write_fmt_literal (fmt : core.fmt.Formatter) (text : Str) :
    fmt.write_fmt (.literal text) = fmt.write_str text := rfl

@[expose, rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  DebugInst.fmt x fmt

@[expose, rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (_ : Bool) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : Unit) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  -- TODO: this is a simplistic model
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::expect"]
def core.result.Result.expect {T : Type} {E : Type} (_DebugInst : core.fmt.Debug E)
  (r : core.result.Result T E) (_ : Str) : Std.Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ =>
    /- TODO: this is a simplistic model -/
    .fail .panic

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish", simp]
def core.fmt.Formatter.debug_struct_field1_finish
  (fmt : core.fmt.Formatter) (_ : Str) (_ : Str) (_ : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish", simp]
def core.fmt.Formatter.debug_struct_field2_finish (fmt : core.fmt.Formatter) (_ : Str)
  (_ : Str) (_ : Dyn (fun dyn => core.fmt.Debug dyn))
  (_ : Str) (_ : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field3_finish", simp]
def core.fmt.Formatter.debug_struct_field3_finish (fmt : core.fmt.Formatter) (_ : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun _ _ _ _ _ _ =>
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish", simp]
def core.fmt.Formatter.debug_struct_field4_finish (fmt : core.fmt.Formatter) (_ : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun _ _ _ _ _ _ _ _ =>
  .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field5_finish", simp]
def core.fmt.Formatter.debug_struct_field5_finish (fmt : core.fmt.Formatter) (_ : Str) :
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Str → Dyn (fun dyn => core.fmt.Debug dyn) →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ _ _ _ _ _ _ _ _ _ => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish", simp]
def core.fmt.Formatter.debug_tuple_field1_finish :
  core.fmt.Formatter → Str → Dyn (fun dyn => core.fmt.Debug dyn) →
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: more precise model that actually uses the `Debug` instance
  fun fmt _ _ =>
  .ok (.Ok (), fmt)

@[expose, reducible, rust_trait_impl "core::fmt::Debug<&'0 @T>"]
def core.fmt.DebugShared {T : Type} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug T := {
  fmt := core.fmt.DebugShared.fmt DebugInst
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<()>"]
def core.fmt.DebugUnit : core.fmt.Debug Unit := {
  fmt := core.fmt.DebugUnit.fmt
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<bool>"]
def core.fmt.DebugBool : core.fmt.Debug Bool := {
  fmt := core.fmt.DebugBool.fmt
}

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"]
def core.fmt.rt.Argument.new_display
  {T : Type} (inst : core.fmt.Display T) (value : T) : Result core.fmt.rt.Argument :=
  .ok ⟨inst.fmt value⟩

theorem core.fmt.rt.Argument.new_display_exact {T : Type}
    (inst : core.fmt.Display T) (value : T) :
    new_display inst value = .ok ⟨inst.fmt value⟩ := rfl

end Aeneas.Std
