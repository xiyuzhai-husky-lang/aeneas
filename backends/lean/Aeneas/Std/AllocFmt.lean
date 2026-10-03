module
public import Aeneas.Std.Scalar.Display
public section

namespace Aeneas.Std

namespace core.fmt.Buffer
@[expose] def encode : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 1 + 257 * encode rest

@[expose] def decode (state : Nat) : List UInt8 :=
  if h : state = 0 then []
  else UInt8.ofNat (state % 257 - 1) :: decode (state / 257)
termination_by state
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

@[simp] theorem decode_encode (bytes : List UInt8) : decode (encode bytes) = bytes := by
  induction bytes with
  | nil => simp [encode, decode]
  | cons byte rest ih =>
      have bound : byte.toNat + 1 < 257 := by have := byte.toNat_lt; omega
      have positive : byte.toNat + 1 + 257 * encode rest ≠ 0 := by omega
      rw [encode, decode]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound,
        Nat.add_mul_div_left, Nat.div_eq_of_lt bound]
      simp [ih]
      all_goals decide

@[expose] def write (state : Nat) (text : Str) :
    Result (core.result.Result Unit core.fmt.Error × Nat) :=
  let bytes := decode state ++ text.val.map (fun byte => UInt8.ofNat byte.val)
  if bytes.length ≤ Usize.max then .ok (.Ok (), encode bytes)
  else .fail .maximumSizeExceeded

@[expose] def initial : core.fmt.Formatter :=
  ⟨core.fmt.defaultOptions, encode [], write⟩

@[expose] def finish (state : Nat) : Result String :=
  match String.fromUTF8? ⟨(decode state).toArray⟩ with
  | some text => .ok text
  | none => .fail .undef
end core.fmt.Buffer

/-- Default/literal formatting into the ordinary logical String buffer.
The original callback Err is mapped to the native format() panic; outer failures
and divergence propagate. Custom-options templates are outside this model's
correspondence fragment. This uses the same normal-allocation boundary as Vec;
it makes no claim that a native allocator cannot abort. -/
@[expose, rust_fun "alloc::fmt::format"]
def alloc.fmt.format (args : core.fmt.Arguments) : Result String := do
  let (outcome, after) ← core.fmt.Buffer.initial.write_fmt args
  match outcome with
  | .Err _ => .fail .panic
  | .Ok () => core.fmt.Buffer.finish after.writerState

end Aeneas.Std
