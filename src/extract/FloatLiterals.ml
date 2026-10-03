(** Decode Charon's decimal literals using exact rational arithmetic and
    round-to-nearest, ties-to-even. No host floating-point operation is used.
    Charon does not retain NaN payload bits in its text format, so NaN literals
    are rejected rather than silently replacing their bit representation. *)

let format (span : Meta.span) (fty : Values.float_type) : int * int =
  match fty with
  | F32 -> (8, 23)
  | F64 -> (11, 52)
  | F16 | F128 -> [%craise] span "Only binary32 and binary64 are supported"

let to_bits (span : Meta.span) (fv : Values.float_value) : Z.t =
  let exponent_bits, fraction_bits = format span fv.float_ty in
  let s = String.lowercase_ascii fv.float_value in
  [%cassert] span (s <> "nan" && s <> "-nan" && s <> "+nan")
    "NaN literal payloads are unavailable in Charon's text float format";
  let s = if s = "+inf" then "inf" else s in
  let negative = String.starts_with ~prefix:"-" s in
  let sign =
    if negative then Z.shift_left Z.one (exponent_bits + fraction_bits)
    else Z.zero
  in
  let bias = (1 lsl (exponent_bits - 1)) - 1 in
  let infinity =
    Z.shift_left (Z.of_int ((1 lsl exponent_bits) - 1)) fraction_bits
  in
  let q =
    try Q.of_string s with
    | Invalid_argument _ | Failure _ ->
        [%craise] span ("Invalid floating-point literal: " ^ fv.float_value)
  in
  let n = Z.abs (Q.num q) and d = Q.den q in
  let magnitude =
    if Z.equal d Z.zero then (
      [%cassert] span (not (Z.equal n Z.zero))
        "NaN literal payloads are unavailable in Charon's text float format";
      infinity)
    else if Z.equal n Z.zero then Z.zero
    else
      let k = Z.numbits n - Z.numbits d in
      let below =
        if k >= 0 then Z.lt n (Z.shift_left d k)
        else Z.lt (Z.shift_left n (-k)) d
      in
      let k = if below then k - 1 else k in
      if k > bias then infinity
      else
        let emin = 1 - bias in
        let scale = max k emin - fraction_bits in
        let n, d =
          if scale >= 0 then (n, Z.shift_left d scale)
          else (Z.shift_left n (-scale), d)
        in
        let m, rem = Z.ediv_rem n d in
        let cmp = Z.compare (Z.shift_left rem 1) d in
        let m =
          if cmp > 0 || (cmp = 0 && Z.testbit m 0) then Z.succ m else m
        in
        if k < emin then m
        else Z.add (Z.shift_left (Z.of_int (k + bias - 1)) fraction_bits) m
  in
  Z.logor sign magnitude
