module
public import Aeneas.Std.Core.Iter
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Scalar.CloneCopy
public section

namespace Aeneas.Std
open Result

/-- Mapping retains the iterator and evolving FnMut closure separately. -/
@[expose, trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.trait_default
    {Self Item B F : Type} (_iter : core.iter.traits.iterator.Iterator Self Item)
    (_call : core.ops.function.FnMut F Item B) (self : Self) (f : F) :
    Result (core.iter.adapters.map.Map Self F) := .ok ⟨self, f⟩

@[expose, rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.IteratorMap.next {B I F Item : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (call : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) :
    Result (Option B × core.iter.adapters.map.Map I F) := do
  let (value, next) ← iter.next self.iter
  match value with
  | none => .ok (none, { self with iter := next })
  | some value =>
    let (mapped, f) ← call.call_mut self.f value
    .ok (some mapped, ⟨next, f⟩)

@[expose, reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>"]
def core.iter.traits.iterator.IteratorMap {B I F Item : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (call : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B := {
  next := core.iter.adapters.map.IteratorMap.next iter call
}

@[rust_type "core::iter::sources::repeat::Repeat"]
structure core.iter.sources.repeat.Repeat (A : Type) where
  element : A

@[expose, rust_fun "core::iter::sources::repeat::repeat"]
def core.iter.sources.repeat.make {T : Type} (_clone : core.clone.Clone T) (element : T) :
    Result (core.iter.sources.repeat.Repeat T) := .ok ⟨element⟩

@[expose, rust_fun
  "core::iter::sources::repeat::{core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>}::next"]
def core.iter.sources.repeat.IteratorRepeat.next {A : Type}
    (clone : core.clone.Clone A) (self : core.iter.sources.repeat.Repeat A) :
    Result (Option A × core.iter.sources.repeat.Repeat A) := do
  let value ← clone.clone self.element
  .ok (some value, self)

@[expose, reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::iter::sources::repeat::Repeat<@A>, @A>"]
def core.iter.traits.iterator.IteratorRepeat {A : Type} (clone : core.clone.Clone A) :
    core.iter.traits.iterator.Iterator (core.iter.sources.repeat.Repeat A) A := {
  next := core.iter.sources.repeat.IteratorRepeat.next clone
}

end Aeneas.Std
