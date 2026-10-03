module
public import Init.Data.BitVec.Lemmas

/-!
Binary32 and binary64 carriers and bit-exact comparisons. These definitions do
not use Lean's opaque host floating-point operations. Arithmetic and numeric
casts are intentionally absent until their rounding semantics are implemented.
-/
@[expose] public section
namespace Aeneas.Std

/-- The complete IEEE encoding, including sign, NaN payload, and signed zero. -/
structure BinaryFloat (exponentBits fractionBits : Nat) where
  bits : BitVec (1 + exponentBits + fractionBits)
  deriving DecidableEq, Inhabited

namespace BinaryFloat
variable {e f : Nat}

def magnitude (x : BinaryFloat e f) : Nat := x.bits.toNat % 2 ^ (e + f)
def sign (x : BinaryFloat e f) : Bool := x.bits.getLsbD (e + f)
def isNaN (x : BinaryFloat e f) : Bool :=
  decide (x.magnitude > (2 ^ e - 1) * 2 ^ f)
def isZero (x : BinaryFloat e f) : Bool := x.magnitude == 0

/-- IEEE equality differs from equality of the encoding. -/
def eq (x y : BinaryFloat e f) : Bool :=
  !x.isNaN && !y.isNaN && (x.bits == y.bits || (x.isZero && y.isZero))
def ne (x y : BinaryFloat e f) : Bool := !(eq x y)

/-- Encoding order agrees with numerical order within each sign; negative
encodings have the reverse order. NaNs are unordered and the zeros compare equal. -/
def lt (x y : BinaryFloat e f) : Bool :=
  !x.isNaN && !y.isNaN && !(x.isZero && y.isZero) &&
    (if x.sign then
       if y.sign then decide (y.magnitude < x.magnitude) else true
     else if y.sign then false else decide (x.magnitude < y.magnitude))
def le (x y : BinaryFloat e f) : Bool := lt x y || eq x y
def gt (x y : BinaryFloat e f) : Bool := lt y x
def ge (x y : BinaryFloat e f) : Bool := le y x

/-- Rust unary negation flips only the sign bit, including for NaNs. -/
def neg (x : BinaryFloat e f) : BinaryFloat e f :=
  ⟨x.bits ^^^ BitVec.ofNat _ (2 ^ (e + f))⟩

@[simp] theorem eq_self (x : BinaryFloat e f) : eq x x = !x.isNaN := by
  simp [eq]
@[simp] theorem eq_nan_left (x y : BinaryFloat e f) (h : x.isNaN = true) :
    eq x y = false := by simp [eq, h]
@[simp] theorem lt_nan_left (x y : BinaryFloat e f) (h : x.isNaN = true) :
    lt x y = false := by simp [lt, h]
@[simp] theorem neg_neg (x : BinaryFloat e f) : neg (neg x) = x := by
  cases x
  simp [neg, BitVec.xor_assoc]
end BinaryFloat

abbrev F32 := BinaryFloat 8 23
abbrev F64 := BinaryFloat 11 52

namespace F32
def ofBits (bits : BitVec 32) : F32 := ⟨bits⟩
def eq (x y : F32) : Bool := BinaryFloat.eq x y
def ne (x y : F32) : Bool := BinaryFloat.ne x y
def lt (x y : F32) : Bool := BinaryFloat.lt x y
def le (x y : F32) : Bool := BinaryFloat.le x y
def gt (x y : F32) : Bool := BinaryFloat.gt x y
def ge (x y : F32) : Bool := BinaryFloat.ge x y
def neg (x : F32) : F32 := BinaryFloat.neg x
end F32

namespace F64
def ofBits (bits : BitVec 64) : F64 := ⟨bits⟩
def eq (x y : F64) : Bool := BinaryFloat.eq x y
def ne (x y : F64) : Bool := BinaryFloat.ne x y
def lt (x y : F64) : Bool := BinaryFloat.lt x y
def le (x y : F64) : Bool := BinaryFloat.le x y
def gt (x y : F64) : Bool := BinaryFloat.gt x y
def ge (x y : F64) : Bool := BinaryFloat.ge x y
def neg (x : F64) : F64 := BinaryFloat.neg x
end F64

end Aeneas.Std
