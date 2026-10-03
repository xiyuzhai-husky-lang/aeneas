module
public import Init.Data.BitVec.Lemmas
public import Init.Data.Nat.Log2

/-!
Binary32 and binary64 carriers and bit-exact comparisons. These definitions do
not use Lean's opaque host floating-point operations. Arithmetic computes with
exact integers and rounds once. Arithmetic NaNs use a representative of the
NaN observation class; bit-observing Rust operations are not supported. The
arithmetic-to-IEEE refinement proof is still an obligation, not an assumption.
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

namespace BinaryFloat
variable {e f : Nat}

/-- Equality of supported observations: all NaN encodings are indistinguishable,
while every non-NaN bit, including the sign of zero, remains significant.
This is not equality of Rust `to_bits` results. -/
def ObsEq (x y : BinaryFloat e f) : Prop :=
  x = y ∨ (x.isNaN = true ∧ y.isNaN = true)

def infinityMagnitude (e f : Nat) : Nat := (2 ^ e - 1) * 2 ^ f
def pack (negative : Bool) (magnitude : Nat) : BinaryFloat e f :=
  ⟨BitVec.ofNat _ ((if negative then 2 ^ (e + f) else 0) + magnitude)⟩
def zero (negative : Bool) : BinaryFloat e f := pack negative 0
def infinity (negative : Bool) : BinaryFloat e f :=
  pack negative (infinityMagnitude e f)
/-- An observation-class representative, not a prediction of a hardware payload. -/
def nan : BinaryFloat e f := pack false (infinityMagnitude e f + 2 ^ (f - 1))
def isInf (x : BinaryFloat e f) : Bool := x.magnitude == infinityMagnitude e f

def bias (e : Nat) : Int := (2 ^ (e - 1) : Nat) - (1 : Int)

/-- For finite inputs, the magnitude is exactly `n * 2^k`. -/
def finiteParts (x : BinaryFloat e f) : Nat × Int :=
  let exponent := x.magnitude / 2 ^ f
  let fraction := x.magnitude % 2 ^ f
  if exponent = 0 then (fraction, 1 - bias e - f)
  else (2 ^ f + fraction, (exponent : Int) - bias e - f)

/-- Round a nonnegative rational to the nearest natural, breaking ties to even.
The caller establishes a nonzero denominator. -/
def roundQuotient (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- Floor of the binary logarithm of a positive rational. -/
def ratioLog2 (n d : Nat) : Int :=
  let k : Int := (n.log2 : Int) - d.log2
  let below := if k ≥ 0 then n < d * 2 ^ k.toNat
               else n * 2 ^ (-k).toNat < d
  if below then k - 1 else k

def roundScaledQuotient (n d : Nat) (shift : Int) : Nat :=
  if shift ≥ 0 then roundQuotient (n * 2 ^ shift.toNat) d
  else roundQuotient n (d * 2 ^ (-shift).toNat)

/-- Encode `(-1)^negative * n/d * 2^exponent` with one nearest-even rounding.
Subnormals share the fixed minimum exponent; a significand carry directly
increments the exponent field, including the carry into infinity. -/
def roundRatio (negative : Bool) (n d : Nat) (exponent : Int) : BinaryFloat e f :=
  if d = 0 then nan
  else if n = 0 then zero negative
  else
    let k := ratioLog2 n d + exponent
    let maxExponent := bias e
    let minExponent := 1 - maxExponent
    if k > maxExponent then infinity negative
    else
      let scale := max k minExponent - f
      let m := roundScaledQuotient n d (exponent - scale)
      let mag := if k < minExponent then m
                 else (k + maxExponent - 1).toNat * 2 ^ f + m
      pack negative mag

/-- IEEE addition at the supported observation level. -/
def add (x y : BinaryFloat e f) : BinaryFloat e f :=
  if x.isNaN || y.isNaN then nan
  else if x.isInf then
    if y.isInf && (x.sign != y.sign) then nan else x
  else if y.isInf then y
  else
    let (nx, ex) := x.finiteParts
    let (ny, ey) := y.finiteParts
    let exponent := min ex ey
    let mx : Int := nx * 2 ^ (ex - exponent).toNat
    let my : Int := ny * 2 ^ (ey - exponent).toNat
    let n := (if x.sign then -mx else mx) + (if y.sign then -my else my)
    let negative := decide (n < 0) || (n == 0 && x.sign && y.sign)
    roundRatio negative n.natAbs 1 exponent

def sub (x y : BinaryFloat e f) : BinaryFloat e f := add x (neg y)

def mul (x y : BinaryFloat e f) : BinaryFloat e f :=
  if x.isNaN || y.isNaN || (x.isInf && y.isZero) || (y.isInf && x.isZero) then nan
  else
    let negative := x.sign ^^ y.sign
    if x.isInf || y.isInf then infinity negative
    else
      let (nx, ex) := x.finiteParts
      let (ny, ey) := y.finiteParts
      roundRatio negative (nx * ny) 1 (ex + ey)

def div (x y : BinaryFloat e f) : BinaryFloat e f :=
  if x.isNaN || y.isNaN || (x.isZero && y.isZero) || (x.isInf && y.isInf) then nan
  else
    let negative := x.sign ^^ y.sign
    if x.isInf || y.isZero then infinity negative
    else if y.isInf then zero negative
    else
      let (nx, ex) := x.finiteParts
      let (ny, ey) := y.finiteParts
      roundRatio negative nx ny (ex - ey)

/-- Rust `%` uses a quotient truncated toward zero, rather than IEEE remainder. -/
def rem (x y : BinaryFloat e f) : BinaryFloat e f :=
  if x.isNaN || y.isNaN || x.isInf || y.isZero then nan
  else if y.isInf || x.isZero then x
  else
    let (nx, ex) := x.finiteParts
    let (ny, ey) := y.finiteParts
    let exponent := min ex ey
    let mx := nx * 2 ^ (ex - exponent).toNat
    let my := ny * 2 ^ (ey - exponent).toNat
    roundRatio x.sign (mx % my) 1 exponent
end BinaryFloat

namespace F32
def add (x y : F32) : F32 := BinaryFloat.add x y
def sub (x y : F32) : F32 := BinaryFloat.sub x y
def mul (x y : F32) : F32 := BinaryFloat.mul x y
def div (x y : F32) : F32 := BinaryFloat.div x y
def rem (x y : F32) : F32 := BinaryFloat.rem x y
end F32

namespace F64
def add (x y : F64) : F64 := BinaryFloat.add x y
def sub (x y : F64) : F64 := BinaryFloat.sub x y
def mul (x y : F64) : F64 := BinaryFloat.mul x y
def div (x y : F64) : F64 := BinaryFloat.div x y
def rem (x y : F64) : F64 := BinaryFloat.rem x y
end F64

end Aeneas.Std
