module
public import Aeneas.Std.String
public import Aeneas.Std.Core.Result
public section
namespace Aeneas.Std
open Result

inductive ParseIntKind where
  | empty | invalidDigit | positiveOverflow
  deriving DecidableEq

@[rust_type "core::num::error::ParseIntError" (body := .opaque)]
structure core.num.error.ParseIntError where
  kind : ParseIntKind

@[rust_trait "core::str::traits::FromStr"]
structure core.str.traits.FromStr (Self Err : Type) where
  from_str : Str → Result (core.result.Result Self Err)

@[expose, rust_fun "core::str::{str}::parse"]
def core.str.Str.parse {Self Err : Type} (parser : core.str.traits.FromStr Self Err)
    (source : Str) : Result (core.result.Result Self Err) := parser.from_str source

def parseDecimalDigits : List U8 → Nat → core.result.Result Nat core.num.error.ParseIntError
  | [], value => .Ok value
  | byte::rest, value =>
    if 48 ≤ byte.val ∧ byte.val ≤ 57 then
      let next := 10*value+(byte.val-48)
      if next ≤ Usize.max then parseDecimalDigits rest next
      else .Err ⟨.positiveOverflow⟩
    else .Err ⟨.invalidDigit⟩

def parseUnsignedBytes (bytes : List U8) : core.result.Result Nat core.num.error.ParseIntError :=
  match bytes with
  | [] => .Err ⟨.empty⟩
  | byte::rest =>
    if byte.val = 43 then
      if rest = [] then .Err ⟨.invalidDigit⟩ else parseDecimalDigits rest 0
    else parseDecimalDigits bytes 0

theorem parseDecimalDigits_bound (bytes : List U8) (initial : Nat) (bounded : initial ≤ Usize.max)
    (value : Nat) (run : parseDecimalDigits bytes initial = .Ok value) : value ≤ Usize.max := by
  induction bytes generalizing initial with
  | nil =>
    simp only [parseDecimalDigits,core.result.Result.Ok.injEq] at run
    simpa only [← run] using bounded
  | cons byte rest ih =>
    simp only [parseDecimalDigits] at run
    split at run
    · split at run
      · exact ih _ (by assumption) run
      · cases run
    · cases run

@[expose, rust_fun "core::num::{core::str::traits::FromStr<usize, core::num::error::ParseIntError>}::from_str"]
def core.num.Usize.from_str (source : Str) : Result (core.result.Result Usize core.num.error.ParseIntError) :=
  match parseUnsignedBytes source.val with
  | .Err error => ok (.Err error)
  | .Ok value =>
    if bounded : value ≤ Usize.max then ok (.Ok (Usize.ofNatCore value (by scalar_tac)))
    else fail .integerOverflow

@[expose, reducible, rust_trait_impl "core::str::traits::FromStr<usize, core::num::error::ParseIntError>"]
def core.str.traits.FromStrUsize : core.str.traits.FromStr Usize core.num.error.ParseIntError :=
  ⟨core.num.Usize.from_str⟩

def decimalValue : List U8 → Nat → Nat
  | [], value => value
  | byte::rest, value => decimalValue rest (10*value+(byte.val-48))

theorem decimalValue_ge (bytes : List U8) (initial : Nat) : initial ≤ decimalValue bytes initial := by
  induction bytes generalizing initial with
  | nil => rfl
  | cons byte rest ih =>
    exact (by omega : initial ≤ 10*initial+(byte.val-48)).trans (ih _)

theorem parseDecimalDigits_value (bytes : List U8) (initial : Nat)
    (digits : ∀ byte ∈ bytes, 48 ≤ byte.val ∧ byte.val ≤ 57)
    (bounded : decimalValue bytes initial ≤ Usize.max) :
    parseDecimalDigits bytes initial = .Ok (decimalValue bytes initial) := by
  induction bytes generalizing initial with
  | nil => rfl
  | cons byte rest ih =>
    have byteGood := digits byte (by simp)
    have nextBound : 10*initial+(byte.val-48) ≤ Usize.max := (decimalValue_ge rest _).trans bounded
    simp only [parseDecimalDigits,byteGood,ite_true,nextBound]
    exact ih _ (fun b member => digits b (by simp only [List.mem_cons]; exact Or.inr member)) bounded

theorem parseDecimalDigits_overflow (bytes : List U8) (initial : Nat)
    (digits : ∀ byte ∈ bytes, 48 ≤ byte.val ∧ byte.val ≤ 57)
    (initialBound : initial ≤ Usize.max) (overflow : Usize.max < decimalValue bytes initial) :
    parseDecimalDigits bytes initial = .Err ⟨.positiveOverflow⟩ := by
  induction bytes generalizing initial with
  | nil => simp only [decimalValue] at overflow; omega
  | cons byte rest ih =>
    have byteGood := digits byte (by simp)
    rw [parseDecimalDigits,if_pos byteGood]
    dsimp only
    split
    · exact ih _ (fun b member => digits b (by simp only [List.mem_cons]; exact Or.inr member)) (by assumption) overflow
    · rfl

theorem parseUnsignedBytes_bound (bytes : List U8) (value : Nat)
    (run : parseUnsignedBytes bytes = .Ok value) : value ≤ Usize.max := by
  cases bytes with
  | nil => cases run
  | cons byte rest =>
    simp only [parseUnsignedBytes] at run
    split at run
    · split at run
      · cases run
      · exact parseDecimalDigits_bound rest 0 (by omega) value run
    · exact parseDecimalDigits_bound (byte::rest) 0 (by omega) value run

theorem core.num.Usize.from_str_total (source : Str) :
    ∃ output, from_str source = ok output := by
  cases run : parseUnsignedBytes source.val with
  | Err error => exact ⟨.Err error,by simp only [from_str,run]⟩
  | Ok value =>
    have bounded := parseUnsignedBytes_bound source.val value run
    refine ⟨.Ok (Usize.ofNatCore value (by scalar_tac)),?_⟩
    simp only [from_str,run,bounded,dite_true]

theorem core.num.Usize.from_str_decimal (source : Str)
    (nonempty : source.val ≠ [])
    (digits : ∀ byte ∈ source.val, 48 ≤ byte.val ∧ byte.val ≤ 57)
    (bounded : decimalValue source.val 0 ≤ Usize.max) :
    ∃ value, from_str source = ok (.Ok value) ∧ value.val = decimalValue source.val 0 := by
  have run := parseDecimalDigits_value source.val 0 digits bounded
  have parsed : parseUnsignedBytes source.val = .Ok (decimalValue source.val 0) := by
    cases shape : source.val with
    | nil => exact False.elim (nonempty shape)
    | cons byte rest =>
      have byteGood := digits byte (by rw [shape]; simp)
      have notPlus : byte.val ≠ 43 := by omega
      simpa only [parseUnsignedBytes,shape,notPlus,ite_false] using run
  refine ⟨Usize.ofNatCore (decimalValue source.val 0) (by scalar_tac),?_,?_⟩
  · simp only [from_str,parsed,bounded,dite_true]
  · exact Usize.ofNatCore_val_eq _

theorem core.num.Usize.from_str_decimal_overflow (source : Str)
    (nonempty : source.val ≠ [])
    (digits : ∀ byte ∈ source.val, 48 ≤ byte.val ∧ byte.val ≤ 57)
    (overflow : Usize.max < decimalValue source.val 0) :
    from_str source = ok (.Err ⟨.positiveOverflow⟩) := by
  have run := parseDecimalDigits_overflow source.val 0 digits (by omega) overflow
  have parsed : parseUnsignedBytes source.val = .Err ⟨.positiveOverflow⟩ := by
    cases shape : source.val with
    | nil => exact False.elim (nonempty shape)
    | cons byte rest =>
      have byteGood := digits byte (by rw [shape]; simp)
      have notPlus : byte.val ≠ 43 := by omega
      simpa only [parseUnsignedBytes,shape,notPlus,ite_false] using run
  simp only [from_str,parsed]

#print axioms core.num.Usize.from_str_total
#print axioms core.num.Usize.from_str_decimal
#print axioms core.num.Usize.from_str_decimal_overflow

end Aeneas.Std
