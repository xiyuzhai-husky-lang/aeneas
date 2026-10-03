module
public import Aeneas.Std.AllocFmt
public import Aeneas.Std.Scalar.Notations
public section

open Aeneas Aeneas.Std
namespace Aeneas.Std

/- Exact contracts for the ordinary default/literal fragment used by the
chapter O source templates. They show these actual templates never enter the
model-coverage failure branch. Custom formatting flags remain outside scope. -/


 theorem core.fmt.bytes_to_native (s : String) :
    (utf8Bytes s).map (fun byte => UInt8.ofNat byte.val) = s.toByteArray.data.toList := by
  simp only [utf8Bytes, List.map_map]
  have equal : ((fun byte : U8 => UInt8.ofNat byte.val) ∘
      (fun x : UInt8 => (⟨x.toNat, by have := x.toNat_lt; simpa using this⟩ : U8))) = id := by
    funext byte
    change UInt8.ofNat byte.toNat = byte
    exact UInt8.ofNat_toNat
  rw [equal, List.map_id]

 theorem core.fmt.Buffer.finish_string (s : String) :
    finish (encode s.toByteArray.data.toList) = .ok s := by
  simp only [finish, decode_encode, Array.toArray_toList]
  change (match String.fromUTF8? s.toByteArray with
    | some text => Result.ok text | none => Result.fail .undef) = .ok s
  rw [String.fromUTF8?, dif_pos s.isValidUTF8]
  rfl

 theorem core.fmt.Buffer.write_string (before text : String)
    (h : (before.toByteArray.data.toList ++ text.toByteArray.data.toList).length ≤ Usize.max)
    (textBound : (core.fmt.utf8Bytes text).length ≤ Usize.max) :
    write (encode before.toByteArray.data.toList) (Slice.from (core.fmt.utf8Bytes text) textBound) =
      .ok (.Ok (), encode (before.toByteArray.data.toList ++ text.toByteArray.data.toList)) := by
  simp only [write, decode_encode, Slice.from_val, core.fmt.bytes_to_native]
  simp only [h, if_pos]

theorem core.fmt.utf8Bytes_length (s : String) :
    (utf8Bytes s).length = s.toByteArray.size := by
  simp [utf8Bytes]

theorem core.fmt.utf8_size_bound (s : String) :
    s.toByteArray.size ≤ 4 * s.length := by
  have lists (chars : List Char) : chars.utf8Encode.size ≤ 4 * chars.length := by
    rw [List.utf8Encode, List.size_toByteArray]
    induction chars with
    | nil => simp
    | cons c cs ih =>
        simp only [List.flatMap_cons, List.length_append, String.length_utf8EncodeChar,
          List.length_cons]
        have := c.utf8Size_le_four
        omega
  simpa only [String.utf8Encode_toList, String.length_toList] using lists s.toList

theorem core.fmt.usize_decimal_bound (value : Usize) :
    (utf8Bytes value.val.repr).length ≤ 80 := by
  rw [utf8Bytes_length]
  have chars : value.val.repr.length ≤ 20 := by
    apply (Nat.length_repr_le_iff (by decide)).mpr
    have h : value.val ≤ Usize.max := by scalar_tac
    rcases Usize.bounds_eq with e | e
    · rw [e, U32.max_eq] at h
      omega
    · rw [e, U64.max_eq] at h
      omega
  have := utf8_size_bound value.val.repr
  omega

set_option maxHeartbeats 1000000 in
theorem alloc.fmt.format_parameter_decimal (number : Nat)
    (bounded : (core.fmt.utf8Bytes number.repr).length ≤ 80) :
    format (.encoded [2#u8,112#u8,33#u8,192#u8,0#u8]
      [⟨core.fmt.displayUnsigned number⟩]) = .ok ("p!" ++ number.repr) := by
  have small : 82 ≤ Usize.max := by scalar_tac
  have decimalBound : (core.fmt.utf8Bytes number.repr).length ≤ Usize.max := by omega
  have appendBound : ([112,33] ++ number.repr.toByteArray.data.toList).length ≤ Usize.max := by
    rw [core.fmt.utf8Bytes_length] at bounded
    simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList]
    change 2 + number.repr.toByteArray.size ≤ Usize.max
    omega
  have byteOrder : ("p!" ++ number.repr).toByteArray.data.toList =
      [112,33] ++ number.repr.toByteArray.data.toList := by
    rw [String.toByteArray_append, ByteArray.toList_data_append]
    rfl
  unfold format core.fmt.Formatter.write_fmt
  change (do
    let (outcome, after) ← core.fmt.writeTemplate 6
      [2#u8,112#u8,33#u8,192#u8,0#u8] [⟨core.fmt.displayUnsigned number⟩] 0
      core.fmt.Buffer.initial
    match outcome with
    | .Err _ => .fail .panic
    | .Ok () => core.fmt.Buffer.finish after.writerState) = _
  rw [core.fmt.writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff,
    Nat.reduceLT, ↓reduceIte, bind_tc_eq, bind_ok, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  simp only [Nat.reduceAdd]
  simp only [core.fmt.literalSlice, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [show 2 ≤ Usize.max by omega, ↓reduceDIte, bind_ok]
  simp only [core.fmt.Formatter.write_str, core.fmt.Buffer.initial,
    core.fmt.Buffer.write, core.fmt.Buffer.decode_encode, Slice.from_val, List.nil_append,
    List.map_cons, List.map_nil, UScalar.ofNatCore_val_eq, List.length_cons, List.length_nil,
    Nat.reduceAdd, show 2 ≤ Usize.max by omega, ↓reduceIte, bind_tc_eq, bind_ok]
  rw [if_neg (show ¬ (2 > (4 : Nat)) by decide)]
  rw [core.fmt.writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte,
    List.getElem?_cons_zero, bind_tc_eq]
  simp only [core.fmt.displayUnsigned, ↓reduceIte, core.fmt.literalSlice,
    decimalBound, ↓reduceDIte, bind_tc_eq, bind_ok]
  simp only [core.fmt.Formatter.write_str, core.fmt.Buffer.write,
    core.fmt.Buffer.decode_encode, Slice.from_val, core.fmt.bytes_to_native,
    bind_tc_eq]
  have appendBound' : ([UInt8.ofNat 112, UInt8.ofNat 33] ++
      number.repr.toByteArray.data.toList).length ≤ Usize.max := by exact appendBound
  rw [if_pos appendBound']
  simp only [bind_ok]
  rw [core.fmt.writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, ↓reduceIte, bind_ok]
  change core.fmt.Buffer.finish (core.fmt.Buffer.encode
    ([112, 33] ++ number.repr.toByteArray.data.toList)) = _
  rw [← byteOrder, core.fmt.Buffer.finish_string]



theorem core.fmt.u32_decimal_bound (value : U32) :
    (utf8Bytes value.val.repr).length ≤ 40 := by
  rw [utf8Bytes_length]
  have chars : value.val.repr.length ≤ 10 := by
    apply (Nat.length_repr_le_iff (by decide)).mpr
    have h : value.val ≤ U32.max := by scalar_tac
    rw [U32.max_eq] at h
    omega
  have := utf8_size_bound value.val.repr
  omega

theorem core.fmt.displayUnsigned_default (number : Nat) (fmt : Formatter)
    (options : fmt.options = defaultOptions)
    (bound : (utf8Bytes number.repr).length ≤ Usize.max) :
    displayUnsigned number fmt = fmt.write_str (.from (utf8Bytes number.repr) bound) := by
  simp only [displayUnsigned, options, ↓reduceIte, literalSlice, bound, ↓reduceDIte,
    bind_tc_eq, bind_ok]

theorem core.fmt.writeTemplate_argument (fuel index : Nat) (argument : rt.Argument)
    (args : List rt.Argument) (fmt : Formatter) (lookup : args[index]? = some argument) :
    writeTemplate (fuel + 2) [192#u8, 0#u8] args index fmt = (do
      let (outcome, after) ← argument.format {fmt with options := defaultOptions}
      .ok (outcome, {fmt with writerState := after.writerState})) := by
  rw [writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte, lookup]
  simp only [bind_tc_eq]
  congr 1
  funext result
  rcases result with ⟨outcome, after⟩
  cases outcome with
  | Err error => rfl
  | Ok trivial =>
      cases trivial
      rw [writeTemplate]
      simp only [UScalar.ofNatCore_val_eq, ↓reduceIte]

theorem alloc.fmt.format_parameter_usize (value : Usize) :
    format (.encoded [2#u8,112#u8,33#u8,192#u8,0#u8]
      [⟨core.fmt.num.imp.DisplayUsize.fmt value⟩]) = .ok ("p!" ++ value.val.repr) :=
  format_parameter_decimal value.val (core.fmt.usize_decimal_bound value)


namespace core.fmt

theorem writeTemplate_unsigned_step (fuel index number : Nat)
    (args : List rt.Argument) (rest : List U8) (before : List UInt8)
    (lookup : args[index]? = some ⟨displayUnsigned number⟩)
    (bound : (before ++ number.repr.toByteArray.data.toList).length ≤ Usize.max) :
    writeTemplate (fuel+1) (192#u8 :: rest) args index
      ⟨defaultOptions, Buffer.encode before, Buffer.write⟩ =
    writeTemplate fuel rest args (index+1)
      ⟨defaultOptions, Buffer.encode (before ++ number.repr.toByteArray.data.toList), Buffer.write⟩ := by
  have decimalBound : (utf8Bytes number.repr).length ≤ Usize.max := by
    rw [utf8Bytes_length]
    simp only [List.length_append, Array.length_toList] at bound
    change before.length + number.repr.toByteArray.size ≤ Usize.max at bound
    omega
  rw [writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte, lookup,
    displayUnsigned, literalSlice, decimalBound, ↓reduceDIte, bind_tc_eq, bind_ok,
    Formatter.write_str, Buffer.write, Buffer.decode_encode, Slice.from_val,
    bytes_to_native, bound]

theorem writeTemplate_literal_step (fuel index : Nat)
    (args : List rt.Argument) (chunk rest : List U8) (before : List UInt8)
    (opcode : U8) (length : opcode.val = chunk.length)
    (nonempty : chunk.length ≠ 0) (small : chunk.length < 128)
    (bound : (before ++ chunk.map (fun byte => UInt8.ofNat byte.val)).length ≤ Usize.max) :
    writeTemplate (fuel+1) (opcode :: (chunk ++ rest)) args index
      ⟨defaultOptions, Buffer.encode before, Buffer.write⟩ =
    writeTemplate fuel rest args index
      ⟨defaultOptions, Buffer.encode (before ++ chunk.map (fun byte => UInt8.ofNat byte.val)),
        Buffer.write⟩ := by
  have notarg : chunk.length ≠ 192 := by omega
  have fits : chunk.length ≤ Usize.max := by
    simp only [List.length_append, List.length_map] at bound
    omega
  have inrest : ¬ (chunk.length > (chunk ++ rest).length) := by simp only [List.length_append];omega
  rw [writeTemplate]
  dsimp only
  simp only [length, nonempty, notarg, small, ↓reduceIte, bind_tc_eq, bind_ok,
    inrest, List.take_left, List.drop_left, literalSlice, fits, ↓reduceDIte,
    Formatter.write_str, Buffer.write, Buffer.decode_encode, Slice.from_val, bound]

end core.fmt


set_option maxHeartbeats 800000 in
theorem alloc.fmt.format_value_u32 (sort index : U32) :
    format (.encoded [7#u8,40#u8,97#u8,115#u8,32#u8,64#u8,118#u8,33#u8,
      192#u8,1#u8,33#u8,192#u8,1#u8,32#u8,0#u8]
      [⟨core.fmt.num.imp.DisplayU32.fmt sort⟩,
       ⟨core.fmt.num.imp.DisplayU32.fmt index⟩]) =
    .ok ("(as @v!" ++ sort.val.repr ++ "!" ++ index.val.repr ++ " ") := by
  have small : 89 ≤ Usize.max := by scalar_tac
  have sortSize := core.fmt.u32_decimal_bound sort
  have indexSize := core.fmt.u32_decimal_bound index
  rw [core.fmt.utf8Bytes_length] at sortSize indexSize
  let startBytes : List UInt8 := [40,97,115,32,64,118,33]
  let args : List core.fmt.rt.Argument := [⟨core.fmt.displayUnsigned sort.val⟩,
    ⟨core.fmt.displayUnsigned index.val⟩]
  have bound1 : (startBytes ++ sort.val.repr.toByteArray.data.toList).length ≤ Usize.max := by
    simp only [startBytes, List.length_append, List.length_cons, List.length_nil, Array.length_toList]
    change 7 + sort.val.repr.toByteArray.size ≤ Usize.max
    omega
  have bound2 : ((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]).length ≤ Usize.max := by
    simp only [startBytes, List.length_append, List.length_cons, List.length_nil, Array.length_toList]
    change 7 + sort.val.repr.toByteArray.size + 1 ≤ Usize.max
    omega
  have bound3 : (((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]) ++
      index.val.repr.toByteArray.data.toList).length ≤ Usize.max := by
    simp only [startBytes, List.length_append, List.length_cons, List.length_nil, Array.length_toList]
    change 7 + sort.val.repr.toByteArray.size + 1 + index.val.repr.toByteArray.size ≤ Usize.max
    omega
  have bound4 : ((((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]) ++
      index.val.repr.toByteArray.data.toList) ++ [32]).length ≤ Usize.max := by
    simp only [startBytes, List.length_append, List.length_cons, List.length_nil, Array.length_toList]
    change 7 + sort.val.repr.toByteArray.size + 1 + index.val.repr.toByteArray.size + 1 ≤ Usize.max
    omega
  unfold format core.fmt.Formatter.write_fmt
  change (do
    let(outcome,after) ← core.fmt.writeTemplate 16
      [7#u8,40#u8,97#u8,115#u8,32#u8,64#u8,118#u8,33#u8,
       192#u8,1#u8,33#u8,192#u8,1#u8,32#u8,0#u8] args 0
       ⟨core.fmt.defaultOptions,core.fmt.Buffer.encode [],core.fmt.Buffer.write⟩
    match outcome with
    | .Err _ => .fail .panic
    | .Ok () => core.fmt.Buffer.finish after.writerState) = _
  erw [core.fmt.writeTemplate_literal_step 15 0 args
    [40#u8,97#u8,115#u8,32#u8,64#u8,118#u8,33#u8]
    [192#u8,1#u8,33#u8,192#u8,1#u8,32#u8,0#u8] [] 7#u8 rfl (by decide) (by decide)
    (by simp only [List.nil_append, List.length_map, List.length_cons, List.length_nil];omega)]
  change (do
    let(outcome,after) ← core.fmt.writeTemplate 15
      [192#u8,1#u8,33#u8,192#u8,1#u8,32#u8,0#u8] args 0
       ⟨core.fmt.defaultOptions,core.fmt.Buffer.encode startBytes,core.fmt.Buffer.write⟩
    match outcome with
    | .Err _ => .fail .panic
    | .Ok () => core.fmt.Buffer.finish after.writerState) = _
  erw [core.fmt.writeTemplate_unsigned_step 14 0 sort.val args
    [1#u8,33#u8,192#u8,1#u8,32#u8,0#u8] startBytes rfl bound1]
  erw [core.fmt.writeTemplate_literal_step 13 1 args [33#u8]
    [192#u8,1#u8,32#u8,0#u8] (startBytes ++ sort.val.repr.toByteArray.data.toList)
    1#u8 rfl (by decide) (by decide) (by exact bound2)]
  erw [core.fmt.writeTemplate_unsigned_step 12 1 index.val args
    [1#u8,32#u8,0#u8] ((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]) rfl bound3]
  erw [core.fmt.writeTemplate_literal_step 11 2 args [32#u8] [0#u8]
    (((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]) ++ index.val.repr.toByteArray.data.toList)
    1#u8 rfl (by decide) (by decide) (by exact bound4)]
  rw [core.fmt.writeTemplate]
  simp only [UScalar.ofNatCore_val_eq, ↓reduceIte, bind_tc_eq, bind_ok]
  have byteOrder : ("(as @v!" ++ sort.val.repr ++ "!" ++ index.val.repr ++ " ").toByteArray.data.toList =
      ((((startBytes ++ sort.val.repr.toByteArray.data.toList) ++ [33]) ++ index.val.repr.toByteArray.data.toList) ++ [32]) := by
    simp only [String.toByteArray_append, ByteArray.toList_data_append]
    rfl
  change core.fmt.Buffer.finish (core.fmt.Buffer.encode _) = _
  erw [← byteOrder, core.fmt.Buffer.finish_string]


namespace core.fmt
/-- A default argument's ordinary formatting error stops before the remaining
bytecode and retains the actual callback's updated sink state. -/
theorem writeTemplate_argument_error (fuel index : Nat) (argument : rt.Argument)
    (args : List rt.Argument) (rest : List U8) (fmt after : Formatter)
    (error : core.fmt.Error) (lookup : args[index]? = some argument)
    (call : argument.format {fmt with options := defaultOptions} = .ok (.Err error, after)) :
    writeTemplate (fuel+1) (192#u8 :: rest) args index fmt =
      .ok (.Err error, {fmt with writerState := after.writerState}) := by
  rw [writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte, lookup,
    call, bind_tc_eq, bind_ok]

theorem writeTemplate_argument_failure (fuel index : Nat) (argument : rt.Argument)
    (args : List rt.Argument) (rest : List U8) (fmt : Formatter)
    (error : Std.Error) (lookup : args[index]? = some argument)
    (call : argument.format {fmt with options := defaultOptions} = .fail error) :
    writeTemplate (fuel+1) (192#u8 :: rest) args index fmt = .fail error := by
  rw [writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte, lookup, call,
    bind_tc_eq, bind_fail]

theorem writeTemplate_argument_divergence (fuel index : Nat) (argument : rt.Argument)
    (args : List rt.Argument) (rest : List U8) (fmt : Formatter)
    (lookup : args[index]? = some argument)
    (call : argument.format {fmt with options := defaultOptions} = .div) :
    writeTemplate (fuel+1) (192#u8 :: rest) args index fmt = .div := by
  rw [writeTemplate]
  dsimp only
  simp only [UScalar.ofNatCore_val_eq, Nat.reduceEqDiff, ↓reduceIte, lookup, call,
    bind_tc_eq, bind_div]
end core.fmt

end Aeneas.Std
