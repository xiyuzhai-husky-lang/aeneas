module
public import Aeneas.Std.Slice
public import Aeneas.Std.Core.Iter
public section

@[expose] section
namespace Aeneas.Std
open Result

/-- The native split iterator retains the unconsumed slice, its stateful
predicate and a finished bit. Finishing does not clear the retained slice. -/
@[rust_type "core::slice::iter::Split"]
structure core.slice.iter.Split (T P : Type) where
  v : Slice T
  pred : P
  finished : Bool

/-- Left-to-right `position` used by `Split::next`. The first matching item is
examined once, the tail is untouched, and every returned closure state is kept. -/
def SliceSplitModel.position {T P : Type} (fn : core.ops.function.FnMut P T Bool) :
    List T → P → Result (Option Nat × P)
  | [], state => ok (none,state)
  | item :: rest, state => do
      let (matched,next) ← fn.call_mut state item
      if matched then ok (some 0,next)
      else
        let (position,finalState) ← position fn rest next
        ok (position.map Nat.succ,finalState)

@[rust_fun "core::slice::{[@T]}::split"]
def core.slice.Slice.split {T P : Type} (_fn : core.ops.function.FnMut P T Bool)
    (self : Slice T) (pred : P) : Result (core.slice.iter.Split T P) :=
  ok ⟨self,pred,false⟩

/-- Prototype standard-library model following `slice/iter.rs::Split::next`.
The delimiter is omitted from both slices. Native unsafe-pointer code is not
itself verified here; callback effects and failures remain ordinary `Result`. -/
@[rust_fun "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Split<'a, @T, @P>, &'a [@T]>}::next"]
def core.slice.iter.Split.next {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : Split T P) : Result (Option (Slice T) × Split T P) := do
  if self.finished then ok (none,self)
  else
    let (found,pred) ← SliceSplitModel.position fn self.v.val self.pred
    match found with
    | none => ok (some self.v,{self with pred, finished := true})
    | some index =>
        let head := Slice.from (self.v.val.take index)
          (by have := self.v.property; simp only [List.length_take]; omega)
        let tail := Slice.from (self.v.val.drop (index + 1))
          (by have := self.v.property; simp only [List.length_drop]; omega)
        ok (some head,{self with v := tail,pred})

@[rust_trait_impl "core::iter::traits::iterator::Iterator<core::slice::iter::Split<'a, @T, @P>, &'a [@T]>"]
def core.iter.traits.iterator.IteratorSplit {T P : Type}
    (fn : core.ops.function.FnMut P T Bool) :
    core.iter.traits.iterator.Iterator (core.slice.iter.Split T P) (Slice T) where
  next := core.slice.iter.Split.next fn
  fold := core.iter.traits.iterator.Iterator.fold.default (core.slice.iter.Split.next fn)

namespace SliceSplitModel

/-- Successful search records every native predicate call, including the one
that consumes a delimiter, with the exact state handed to the following call. -/
inductive PositionTrace {T P : Type} (fn : core.ops.function.FnMut P T Bool) :
    List T → P → Option Nat → P → Prop where
  | nil (state : P) : PositionTrace fn [] state none state
  | found (item : T) (rest : List T) (state next : P)
      (call : fn.call_mut state item = ok (true,next)) :
      PositionTrace fn (item :: rest) state (some 0) next
  | skip (item : T) (rest : List T) (state next finalState : P) (index : Option Nat)
      (call : fn.call_mut state item = ok (false,next))
      (later : PositionTrace fn rest next index finalState) :
      PositionTrace fn (item :: rest) state (index.map Nat.succ) finalState

theorem position_of_trace {T P : Type} {fn : core.ops.function.FnMut P T Bool}
    {items : List T} {state finalState : P} {index : Option Nat}
    (trace : PositionTrace fn items state index finalState) :
    position fn items state = ok (index,finalState) := by
  induction trace with
  | nil => rfl
  | found item rest state next call => simp [position,call]
  | skip item rest state next finalState index call later ih => simp [position,call,ih]

theorem position_trace_of_ok {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (items : List T) (state finalState : P) (index : Option Nat)
    (run : position fn items state = ok (index,finalState)) :
    PositionTrace fn items state index finalState := by
  induction items generalizing state finalState index with
  | nil =>
      simp only [position,Result.ok.injEq,Prod.mk.injEq] at run
      rcases run with ⟨rfl,rfl⟩
      exact .nil _
  | cons item rest ih =>
      cases call : fn.call_mut state item with
      | vis eff k => simp [position,call] at run
      | div => simp [position,call] at run
      | ret result =>
          rcases result with ⟨matched,next⟩
          cases matched with
          | true =>
              simp only [position,call,bind_tc_ok,↓reduceIte,Result.ok.injEq,Prod.mk.injEq] at run
              rcases run with ⟨rfl,rfl⟩
              exact .found item rest state next call
          | false =>
              cases tail : position fn rest next with
              | vis eff k => simp [position,call,tail] at run
              | div => simp [position,call,tail] at run
              | ret result =>
                  rcases result with ⟨found,ending⟩
                  simp only [position,call,bind_tc_ok,Bool.false_eq_true,↓reduceIte,tail,
                    Result.ok.injEq,Prod.mk.injEq] at run
                  rcases run with ⟨rfl,rfl⟩
                  exact .skip item rest state next ending found call (ih next ending found tail)

theorem position_spec {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (items : List T) (state finalState : P) (index : Option Nat) :
    position fn items state = ok (index,finalState) ↔ PositionTrace fn items state index finalState :=
  ⟨position_trace_of_ok fn items state finalState index,position_of_trace⟩

theorem PositionTrace.index_bound {T P : Type} {fn : core.ops.function.FnMut P T Bool}
    {items : List T} {state finalState : P} {index : Option Nat}
    (trace : PositionTrace fn items state index finalState) :
    ∀ i, index = some i → i < items.length := by
  induction trace with
  | nil => simp
  | found => intro i same; simp at same; simp [← same]
  | skip item rest state next finalState index call later ih =>
      intro i same
      cases index with
      | none => simp at same
      | some j => simp only [Option.map_some,Option.some.injEq] at same; subst i; simpa using Nat.succ_lt_succ (ih j rfl)

/-- Pure predicates recover the ordinary first-matching-index operation and
leave their owned state unchanged. This is a corollary of the stateful model. -/
theorem position_stateless {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (test : T → Bool) (pureCall : ∀ state item, fn.call_mut state item = ok (test item,state))
    (items : List T) (state : P) :
    position fn items state = ok (items.findIdx? test,state) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
      simp only [position,pureCall,bind_tc_ok,List.findIdx?_cons]
      cases test item <;> simp [ih]

theorem position_callback_fail {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (item : T) (rest : List T) (state : P) (error : Error)
    (failed : fn.call_mut state item = fail error) :
    position fn (item :: rest) state = fail error := by simp [position,failed]

theorem position_callback_div {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (item : T) (rest : List T) (state : P)
    (diverged : fn.call_mut state item = div) :
    position fn (item :: rest) state = div := by simp [position,diverged]

theorem next_finished {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (finished : self.finished = true) :
    core.slice.iter.Split.next fn self = ok (none,self) := by
  simp [core.slice.iter.Split.next,finished]

theorem next_no_delimiter {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (pred : P) (active : self.finished = false)
    (scan : position fn self.v.val self.pred = ok (none,pred)) :
    core.slice.iter.Split.next fn self = ok (some self.v,{self with pred,finished := true}) := by
  simp [core.slice.iter.Split.next,active,scan]

theorem next_delimiter {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (pred : P) (index : Nat) (active : self.finished = false)
    (scan : position fn self.v.val self.pred = ok (some index,pred)) :
    ∃ head tail, core.slice.iter.Split.next fn self = ok (some head,{self with v := tail,pred}) ∧
      head.val = self.v.val.take index ∧ tail.val = self.v.val.drop (index + 1) ∧
      index < self.v.val.length := by
  have bound := (position_trace_of_ok fn _ _ _ _ scan).index_bound index rfl
  simp only [core.slice.iter.Split.next,active,Bool.false_eq_true,↓reduceIte,scan,bind_tc_ok]
  exact ⟨_,_,rfl,by simp,by simp,bound⟩

theorem next_empty {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (active : self.finished = false) (empty : self.v.val = []) :
    core.slice.iter.Split.next fn self = ok (some self.v,{self with finished := true}) := by
  simpa using next_no_delimiter fn self self.pred active (by simp [empty,position])

theorem next_scan_fail {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (error : Error) (active : self.finished = false)
    (scan : position fn self.v.val self.pred = fail error) :
    core.slice.iter.Split.next fn self = fail error := by simp [core.slice.iter.Split.next,active,scan]

theorem next_scan_div {T P : Type} (fn : core.ops.function.FnMut P T Bool)
    (self : core.slice.iter.Split T P) (active : self.finished = false)
    (scan : position fn self.v.val self.pred = div) :
    core.slice.iter.Split.next fn self = div := by simp [core.slice.iter.Split.next,active,scan]

end SliceSplitModel
end Aeneas.Std
