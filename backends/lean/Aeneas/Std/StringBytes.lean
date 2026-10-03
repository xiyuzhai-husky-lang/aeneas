module
public import Aeneas.Std.String
public import Aeneas.Std.Vec
public section
namespace Aeneas.Std
open Result

/-- Exact UTF-8 bytes of the logical Rust String value. -/
def alloc.string.String.utf8Bytes (s : String) : List U8 :=
  s.toByteArray.toList.map (fun x => ⟨x.toNat, by
    cases x
    simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]
    omega⟩)

/-- Native `into_bytes` transfers its existing allocation without changing the
bytes. The bound expresses validity of the native String carrier; this operation
neither allocates nor decodes/re-encodes its UTF-8 contents. -/
@[expose, rust_fun "alloc::string::{alloc::string::String}::into_bytes"]
def alloc.string.String.into_bytes (s : String) : Result (alloc.vec.Vec U8) :=
  let bytes := utf8Bytes s
  if bounded : bytes.length ≤ Usize.max then ok (alloc.vec.Vec.from bytes bounded)
  else fail .maximumSizeExceeded

theorem alloc.string.String.into_bytes_exact (s : String)
    (bounded : (utf8Bytes s).length ≤ Usize.max) :
    into_bytes s = ok (alloc.vec.Vec.from (utf8Bytes s) bounded) := by
  simp [into_bytes, bounded]

theorem alloc.string.String.into_bytes_contents (s : String)
    (bounded : (utf8Bytes s).length ≤ Usize.max) :
    ∃ bytes, into_bytes s = ok bytes ∧ bytes.val = utf8Bytes s := by
  exact ⟨alloc.vec.Vec.from (utf8Bytes s) bounded, into_bytes_exact s bounded, alloc.vec.Vec.from_val _ _⟩
/-- Borrow the unchanged UTF-8 contents of a valid native String. -/
@[expose, rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
def alloc.string.String.as_bytes (s : String) : Result (Slice U8) :=
  let bytes := utf8Bytes s
  if bounded : bytes.length ≤ Usize.max then ok (Slice.from bytes bounded)
  else fail .maximumSizeExceeded

theorem alloc.string.String.as_bytes_exact (s : String)
    (bounded : (utf8Bytes s).length ≤ Usize.max) :
    as_bytes s = ok (Slice.from (utf8Bytes s) bounded) := by
  simp [as_bytes, bounded]

end Aeneas.Std
