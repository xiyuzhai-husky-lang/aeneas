module
public import Floats

public section
open Aeneas Aeneas.Std

namespace floats.tests

-- These proofs reduce the extracted Rust definitions in the Lean kernel.
theorem comparisons_pass : comparisons = .ok () := by
  simp [comparisons, eq32, ne32, lt32, le32, gt32, ge32, neg32,
    eq64, ne64, lt64, le64, gt64, ge64, neg64,
    F32.eq, F32.ne, F32.lt, F32.le, F32.gt, F32.ge, F32.neg,
    F64.eq, F64.ne, F64.lt, F64.le, F64.gt, F64.ge, F64.neg,
    F32.ofBits, F64.ofBits, BinaryFloat.eq, BinaryFloat.ne,
    BinaryFloat.lt, BinaryFloat.le, BinaryFloat.gt, BinaryFloat.ge,
    BinaryFloat.neg, BinaryFloat.isNaN, BinaryFloat.isZero,
    BinaryFloat.magnitude, BinaryFloat.sign, massert]

theorem constants32_bits : constants32 = .ok
    (F32.ofBits 0x00000000, F32.ofBits 0x80000000, F32.ofBits 0x3dcccccd,
     F32.ofBits 0x00800000, F32.ofBits 0x7f7fffff, F32.ofBits 0x00000001) := by rfl

theorem constants64_bits : constants64 = .ok
    (F64.ofBits 0x0000000000000000, F64.ofBits 0x8000000000000000,
     F64.ofBits 0x3fb999999999999a, F64.ofBits 0x0010000000000000,
     F64.ofBits 0x7fefffffffffffff, F64.ofBits 0x0000000000000001) := by rfl

theorem eq32_self (x : F32) : eq32 x x = .ok (!x.isNaN) := by
  simp [eq32, F32.eq]
theorem eq64_self (x : F64) : eq64 x x = .ok (!x.isNaN) := by
  simp [eq64, F64.eq]

theorem neg32_twice (x : F32) : (do let y ← neg32 x; neg32 y) = .ok x := by
  simp [neg32, F32.neg]
theorem neg64_twice (x : F64) : (do let y ← neg64 x; neg64 y) = .ok x := by
  simp [neg64, F64.neg]

-- NaN payloads are supplied as arbitrary model inputs. Charon's text literals
-- lose NaN payloads; this patch deliberately rejects such literals.
theorem nan32_unordered :
    eq32 (F32.ofBits 0x7fc00001) (F32.ofBits 0x7fc00001) = .ok false ∧
    ne32 (F32.ofBits 0x7fc00001) (F32.ofBits 0x7fc00001) = .ok true ∧
    le32 (F32.ofBits 0x7fc00001) (F32.ofBits 0) = .ok false ∧
    ge32 (F32.ofBits 0) (F32.ofBits 0x7fc00001) = .ok false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem nan64_unordered :
    eq64 (F64.ofBits 0xfff0000000000001) (F64.ofBits 0xfff0000000000001) = .ok false ∧
    ne64 (F64.ofBits 0xfff0000000000001) (F64.ofBits 0xfff0000000000001) = .ok true ∧
    le64 (F64.ofBits 0xfff0000000000001) (F64.ofBits 0) = .ok false ∧
    ge64 (F64.ofBits 0) (F64.ofBits 0xfff0000000000001) = .ok false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem special_order32 :
    lt32 (F32.ofBits 0xff800000) (F32.ofBits 0xff7fffff) = .ok true ∧
    lt32 (F32.ofBits 0x80000001) (F32.ofBits 0x80000000) = .ok true ∧
    eq32 (F32.ofBits 0) (F32.ofBits 0x80000000) = .ok true ∧
    lt32 (F32.ofBits 0) (F32.ofBits 1) = .ok true ∧
    lt32 (F32.ofBits 0x7f7fffff) (F32.ofBits 0x7f800000) = .ok true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem special_order64 :
    lt64 (F64.ofBits 0xfff0000000000000) (F64.ofBits 0xffefffffffffffff) = .ok true ∧
    lt64 (F64.ofBits 0x8000000000000001) (F64.ofBits 0x8000000000000000) = .ok true ∧
    eq64 (F64.ofBits 0) (F64.ofBits 0x8000000000000000) = .ok true ∧
    lt64 (F64.ofBits 0) (F64.ofBits 1) = .ok true ∧
    lt64 (F64.ofBits 0x7fefffffffffffff) (F64.ofBits 0x7ff0000000000000) = .ok true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms comparisons_pass
#print axioms constants32_bits
#print axioms constants64_bits
#print axioms eq32_self
#print axioms eq64_self
#print axioms neg32_twice
#print axioms neg64_twice
#print axioms nan32_unordered
#print axioms nan64_unordered
#print axioms special_order32
#print axioms special_order64
theorem infinities32_bits : infinities32 = .ok
    (F32.ofBits 0x7f800000, F32.ofBits 0xff800000) := by rfl

theorem infinities64_bits : infinities64 = .ok
    (F64.ofBits 0x7ff0000000000000, F64.ofBits 0xfff0000000000000) := by rfl

#print axioms infinities32_bits
#print axioms infinities64_bits
end floats.tests
