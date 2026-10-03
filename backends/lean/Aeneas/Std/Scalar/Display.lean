module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Fmt
public section

namespace Aeneas.Std

@[expose] def core.fmt.utf8Bytes (s : String) : List U8 :=
  s.toByteArray.data.toList.map (fun x => ⟨x.toNat, by
    cases x
    simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]
    omega⟩)

/-- Decimal formatting for an unsigned value at default options. The custom
options branch is deliberately outside this model's correspondence fragment. -/
@[expose] def core.fmt.displayUnsigned (value : Nat) (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) := do
  if fmt.options = core.fmt.defaultOptions then
    let text ← core.fmt.literalSlice (core.fmt.utf8Bytes value.repr)
    fmt.write_str text
  else .fail .undef


@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u8>}::fmt", simp]
def core.fmt.num.imp.DisplayU8.fmt : Std.U8 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u16>}::fmt", simp]
def core.fmt.num.imp.DisplayU16.fmt : Std.U16 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u32>}::fmt"]
def core.fmt.num.imp.DisplayU32.fmt (value : U32) (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  core.fmt.displayUnsigned value.val fmt

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u64>}::fmt", simp]
def core.fmt.num.imp.DisplayU64.fmt : Std.U64 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<u128>}::fmt", simp]
def core.fmt.num.imp.DisplayU128.fmt : Std.U128 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<usize>}::fmt"]
def core.fmt.num.imp.DisplayUsize.fmt (value : Usize) (fmt : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  core.fmt.displayUnsigned value.val fmt

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i8>}::fmt", simp]
def core.fmt.num.imp.DisplayI8.fmt : Std.I8 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i16>}::fmt", simp]
def core.fmt.num.imp.DisplayI16.fmt : Std.I16 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i32>}::fmt", simp]
def core.fmt.num.imp.DisplayI32.fmt : Std.I32 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i64>}::fmt", simp]
def core.fmt.num.imp.DisplayI64.fmt : Std.I64 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<i128>}::fmt", simp]
def core.fmt.num.imp.DisplayI128.fmt : Std.I128 → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

@[expose, rust_fun "core::fmt::num::imp::{core::fmt::Display<isize>}::fmt", simp]
def core.fmt.num.imp.DisplayIsize.fmt : Std.Isize → core.fmt.Formatter →
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ fmt => .ok (.Ok (), fmt)

end Aeneas.Std
