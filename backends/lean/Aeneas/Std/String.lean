module
public import Aeneas.Std.Scalar
public import Aeneas.Std.Slice
public import Aeneas.Std.StringDef
public section

namespace Aeneas.Std

instance : DecidableEq Str := inferInstanceAs (DecidableEq (Slice U8))

/-- `bs.toList` has the same length as `bs`. -/
theorem ByteArray.length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  have loop_length :
      ∀ (i : Nat) (r : List UInt8), i ≤ bs.size →
        (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      have hi' : i + 1 ≤ bs.size := by scalar_tac
      rw [ih hi']
      simp; scalar_tac
    | case2 i r h =>
      simp; scalar_tac
  unfold ByteArray.toList
  rw [loop_length 0 [] (Nat.zero_le _)]
  simp

/-- Literal length bounds are checked by the kernel after reducing scalar bounds. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by scalar_tac_preprocess; decide) : Str :=
  .from (s.toByteArray.toList.map
    (fun x => ⟨ x.toNat, by cases x; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega  ⟩))
    (by
      simp only [UScalarTy.U8_numBits_eq, Nat.reducePow, Fin.mk_uInt8ToNat, BitVec.ofFin_uInt8ToFin,
        List.length_map]
      rw [ByteArray.length_toList]
      exact h.trans (by scalar_tac))

example : Str := toStr "hello"

 theorem ByteArray.contents_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
   have loop : ∀ (i : Nat) (r : List UInt8),
       ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
     intro i r
     fun_induction ByteArray.toList.loop bs i r with
     | case1 i r hi ih =>
       rw [ih]
       conv_rhs => rw [List.drop_eq_getElem_cons (by simpa [← ByteArray.size_data] using hi)]
       simp [List.reverse_cons, List.append_assoc, ByteArray.get!, hi]
       rfl
     | case2 i r hi =>
       have length : bs.data.toList.length = bs.size := by
         rw [Array.length_toList]; rfl
       rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
   simpa [ByteArray.toList] using loop 0 []
 theorem toStr_byteArray_roundtrip (s : String) (h : s.toByteArray.size ≤ U32.max) :
     (((toStr s h).val).map (fun b => UInt8.ofNat b.val)).toByteArray = s.toByteArray := by
   apply ByteArray.ext
   apply Array.ext'
   simp only [toStr, Slice.from_val, List.toList_data_toByteArray, List.map_map]
   change (s.toByteArray.toList.map fun b => UInt8.ofNat (⟨b.toNat, _⟩ : U8).val) = _
   have roundtrip : ∀ b : UInt8, UInt8.ofNat (⟨b.toNat, by cases b; simp; omega⟩ : U8).val = b := by
     intro b
     cases b
     simp [UScalar.val]
   have identity : (fun b : UInt8 => UInt8.ofNat (⟨b.toNat, by cases b; simp; omega⟩ : U8).val) = id := by
     funext b; exact roundtrip b
   rw [identity, List.map_id]
   exact ByteArray.contents_toList s.toByteArray


end Aeneas.Std
