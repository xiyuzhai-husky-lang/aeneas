module
public import Aeneas.Std.String
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.SliceIter
public section

namespace Aeneas.Std

@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  iter : core.slice.iter.Iter U8

/-- The UTF-8 window beginning at the native iterator's current byte position.
The byte slice model also admits invalid UTF-8; those states fail explicitly. -/
def core.str.iter.Chars.remainingBytes (it : core.str.iter.Chars) : ByteArray :=
  ((it.iter.slice.val.drop it.iter.i).map (fun b => UInt8.ofNat b.val)).toByteArray

@[expose, rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::next"]
def core.str.iter.IteratorChars.next (it : core.str.iter.Chars) :
    Result ((Option Char) × core.str.iter.Chars) :=
  if it.iter.i < it.iter.slice.val.length then
    match it.remainingBytes.utf8DecodeChar? 0 with
    | some ch => .ok (some ch, { iter := { it.iter with i := it.iter.i + ch.utf8Size } })
    | none => .fail .panic
  else .ok (none, it)

theorem core.str.iter.IteratorChars.next_decoded (it : core.str.iter.Chars)
    (ch : Char) (pending : it.iter.i < it.iter.slice.val.length)
    (decoded : it.remainingBytes.utf8DecodeChar? 0 = some ch) :
    next it = .ok (some ch, { iter := { it.iter with i := it.iter.i + ch.utf8Size } }) := by
  simp only [next, pending, if_true, decoded]

theorem core.str.iter.IteratorChars.next_exhausted (it : core.str.iter.Chars)
    (finished : it.iter.slice.val.length ≤ it.iter.i) :
    next it = .ok (none, it) := by
  simp only [next, Nat.not_lt.mpr finished, if_false]

theorem core.str.iter.IteratorChars.next_invalid (it : core.str.iter.Chars)
    (pending : it.iter.i < it.iter.slice.val.length)
    (invalid : it.remainingBytes.utf8DecodeChar? 0 = none) :
    next it = .fail .panic := by
  simp only [next, pending, if_true, invalid]

@[expose, reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>"]
def core.iter.traits.iterator.IteratorChars :
  core.iter.traits.iterator.Iterator core.str.iter.Chars Char := {
  next := core.str.iter.IteratorChars.next
  -- Chars uses the native default fold; callback state is retained.
  fold := core.iter.traits.iterator.Iterator.fold.default core.str.iter.IteratorChars.next
}

@[expose, rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
def core.str.iter.IteratorChars.collect
    {B : Type} (collector : core.iter.traits.collect.FromIterator B Char)
    (it : core.str.iter.Chars) : Result B :=
  core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.iterator.IteratorChars collector it

@[expose, rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : Result core.str.iter.Chars :=
  .ok { iter := { slice := s, i := 0 } }

 theorem core.str.iter.Chars.remainingBytes_size (it : core.str.iter.Chars) :
     it.remainingBytes.size = it.iter.slice.val.length - it.iter.i := by
   simp [remainingBytes]
 theorem core.str.iter.Chars.remainingBytes_advance (it : core.str.iter.Chars) (n : Nat) :
     (core.str.iter.Chars.mk { it.iter with i := it.iter.i + n }).remainingBytes.data.toList =
       it.remainingBytes.data.toList.drop n := by
   simp only [remainingBytes, List.toList_data_toByteArray]
   rw [← List.drop_drop, List.map_drop]
 theorem core.str.iter.IteratorChars.next_utf8 (it : core.str.iter.Chars) (ch : Char)
     (tail : List Char) (valid : it.remainingBytes = (ch :: tail).utf8Encode) :
     ∃ rest, next it = .ok (some ch, rest) ∧
       rest.remainingBytes = tail.utf8Encode ∧
       rest.iter.i = it.iter.i + ch.utf8Size := by
   have decoded : it.remainingBytes.utf8DecodeChar? 0 = some ch := by
     rw [valid]; exact List.utf8DecodeChar?_utf8Encode_cons
   have bytesEnough := ByteArray.le_size_of_utf8DecodeChar?_eq_some decoded
   rw [core.str.iter.Chars.remainingBytes_size] at bytesEnough
   have pending : it.iter.i < it.iter.slice.val.length := by
     have := ch.utf8Size_pos
     omega
   refine ⟨{ iter := { it.iter with i := it.iter.i + ch.utf8Size } },
     next_decoded it ch pending decoded, ?_, rfl⟩
   apply ByteArray.ext
   apply Array.ext'
   rw [core.str.iter.Chars.remainingBytes_advance, valid, List.utf8Encode_cons,
       ByteArray.toList_data_append]
   simp [List.utf8Encode, String.length_utf8EncodeChar]

/-- Constructing `chars` from a valid logical Rust string retains exactly its
Unicode scalar sequence, including two-, three- and four-byte characters. -/
theorem core.str.Str.chars_unicode (s : String)
    (bounded : s.toByteArray.size ≤ U32.max) :
    ∃ it, chars (toStr s bounded) = .ok it ∧
      it.remainingBytes = s.toList.utf8Encode := by
  refine ⟨{ iter := { slice := toStr s bounded, i := 0 } }, rfl, ?_⟩
  simp only [core.str.iter.Chars.remainingBytes, List.drop_zero]
  rw [toStr_byteArray_roundtrip, String.utf8Encode_toList]

theorem core.str.iter.IteratorChars.next_utf8_empty (it : core.str.iter.Chars)
    (empty : it.remainingBytes = ([] : List Char).utf8Encode) :
    next it = .ok (none, it) := by
  have size := congrArg ByteArray.size empty
  simp only [core.str.iter.Chars.remainingBytes_size, List.utf8Encode,
    List.flatMap_nil, List.toByteArray_nil, ByteArray.size_empty] at size
  apply next_exhausted
  omega

end Aeneas.Std
