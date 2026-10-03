module
public import Aeneas.Std.Vec
@[expose] public section

open Aeneas Aeneas.Std Result
namespace Aeneas.Std

/-- Reservation failures observable by the response codec. Allocation layout
and allocator-private error payloads are erased: this binding covers clients
that discard that payload, not Rust error formatting, equality, or `kind` APIs. -/
@[rust_type "alloc::collections::TryReserveError"]
inductive alloc.collections.TryReserveError where
  | capacityOverflow
  | allocError

/-- An explicit resource-result boundary, with no global instance. The native
library preserves vector contents, accepts a zero request, and cannot reserve
an overflowing element count. Other outcomes are supplied, not forced to succeed.

This length-indexed oracle is not a model of allocator state or vector capacity.
For the response Writer, a successful nonzero append strictly increases length;
a failed reservation exits immediately, and zero reservations always succeed.
Thus each nonzero query occurs at most once in one Writer execution, permitting
its native outcome trace to instantiate this interface consistently. General
clients with repeated queries or observable error payloads need a richer boundary. -/
class ReservationModel where
  reserve : Usize → Usize → core.result.Result Unit alloc.collections.TryReserveError
  reserve_zero (current : Usize) : reserve current 0#usize = .Ok ()
  reserve_overflow (current additional : Usize)
    (overflow : Usize.max < current.val + additional.val) :
    reserve current additional = .Err .capacityOverflow

/-- Logical contents contract for native `Vec::try_reserve`. Native capacity,
layout and resource availability are represented only by the explicit outcome
parameter above. Both native success and failure return the original contents. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::try_reserve"
  (keepParams := [true, false])]
def alloc.vec.Vec.try_reserve {T : Type} [ReservationModel]
    (self : alloc.vec.Vec T) (additional : Usize) :
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T) :=
  ok (ReservationModel.reserve (alloc.vec.Vec.len self) additional, self)

namespace VecReservation
variable {T : Type} [ReservationModel]

theorem try_reserve_exact (self : alloc.vec.Vec T) (additional : Usize) :
    self.try_reserve additional =
      ok (ReservationModel.reserve (alloc.vec.Vec.len self) additional, self) := rfl

theorem try_reserve_success (self : alloc.vec.Vec T) (additional : Usize)
    (success : ReservationModel.reserve (alloc.vec.Vec.len self) additional = .Ok ()) :
    self.try_reserve additional = ok (.Ok (), self) := by
  simp [alloc.vec.Vec.try_reserve, success]

theorem try_reserve_failure (self : alloc.vec.Vec T) (additional : Usize)
    (error : alloc.collections.TryReserveError)
    (failure : ReservationModel.reserve (alloc.vec.Vec.len self) additional = .Err error) :
    self.try_reserve additional = ok (.Err error, self) := by
  simp [alloc.vec.Vec.try_reserve, failure]

/-- A returned reservation error is an ordinary inner Rust error. It neither
becomes an Aeneas failure nor changes the vector's stored elements. -/
theorem try_reserve_contents (self after : alloc.vec.Vec T) (additional : Usize)
    (outcome : core.result.Result Unit alloc.collections.TryReserveError)
    (run : self.try_reserve additional = ok (outcome, after)) :
    after = self ∧ outcome = ReservationModel.reserve (alloc.vec.Vec.len self) additional := by
  simpa [alloc.vec.Vec.try_reserve, eq_comm, and_comm] using run

theorem try_reserve_zero (self : alloc.vec.Vec T) :
    self.try_reserve 0#usize = ok (.Ok (), self) := by
  simp [alloc.vec.Vec.try_reserve, ReservationModel.reserve_zero]

theorem try_reserve_overflow (self : alloc.vec.Vec T) (additional : Usize)
    (overflow : Usize.max < self.val.length + additional.val) :
    self.try_reserve additional = ok (.Err .capacityOverflow, self) := by
  apply try_reserve_failure
  apply ReservationModel.reserve_overflow
  simpa using overflow

theorem try_reserve_success_fits (self : alloc.vec.Vec T) (additional : Usize)
    (success : self.try_reserve additional = ok (.Ok (), self)) :
    self.val.length + additional.val ≤ Usize.max := by
  by_contra overflow
  have failed := try_reserve_overflow self additional (Nat.lt_of_not_ge overflow)
  rw [success] at failed
  simp at failed

#print axioms try_reserve_success
#print axioms try_reserve_failure
#print axioms try_reserve_contents
#print axioms try_reserve_zero
#print axioms try_reserve_overflow
#print axioms try_reserve_success_fits
end VecReservation
end Aeneas.Std
