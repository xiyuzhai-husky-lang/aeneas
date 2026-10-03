module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Slice
@[expose] public section

namespace Aeneas.Std

@[rust_trait "core::hash::Hasher"]
structure core.hash.Hasher (Self : Type) where
  finish : Self → Result U64
  write : Self → Slice U8 → Result Self
  /-- Keep integer dispatch: a Hasher may override this independently of write. -/
  write_u32 : Self → U32 → Result Self

@[rust_trait "core::hash::Hash"]
structure core.hash.Hash (Self : Type) where
  hash : forall {H : Type}, core.hash.Hasher H → Self → H → Result H

/-- Rust's u32 Hash implementation dispatches to the supplied write_u32 method. -/
@[rust_fun "core::hash::impls::{core::hash::Hash<u32>}::hash"]
def core.hash.hashU32 {H : Type} (inst : core.hash.Hasher H) (x : U32) (state : H) :
    Result H := inst.write_u32 state x

theorem core.hash.hashU32_dispatch {H : Type} (inst : core.hash.Hasher H)
    (x : U32) (state : H) : hashU32 inst x state = inst.write_u32 state x := rfl

theorem core.hash.hashU32_spec {H : Type} (inst : core.hash.Hasher H)
    (x : U32) (state out : H) (h : inst.write_u32 state x = .ok out) :
    hashU32 inst x state = .ok out := h

end Aeneas.Std
