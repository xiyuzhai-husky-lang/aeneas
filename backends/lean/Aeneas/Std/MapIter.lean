module
public import Aeneas.Std.Core.Iter
public section

@[expose] section
namespace Aeneas.Std
open Result

/-- `Iterator::map` stores the iterator and its owned stateful closure. -/
@[rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
    {I Item B F : Type} (_iter : core.iter.traits.iterator.Iterator I Item)
    (_fn : core.ops.function.FnMut F Item B) (self : I) (f : F) :
    Result (core.iter.adapters.map.Map I F) :=
  ok ⟨self, f⟩

/-- `Map::next`: the source advances before the callback, and the returned
closure state becomes the next map state. An exhausted source does not call it. -/
@[rust_fun "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.Map.next {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (fn : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) :
    Result (Option B × core.iter.adapters.map.Map I F) := do
  let (item, source) ← iter.next self.iter
  match item with
  | none => ok (none, ⟨source, self.f⟩)
  | some item =>
    let (result, state) ← fn.call_mut self.f item
    ok (some result, ⟨source, state⟩)

/-- The native `map_fold` closure holds both evolving callback states. -/
def IteratorPrototype.mapFoldCall {Item B Acc F G : Type}
    (mapFn : core.ops.function.FnMut F Item B)
    (foldFn : core.ops.function.FnMut G (Acc × B) Acc)
    (state : F × G) (input : Acc × Item) : Result (Acc × (F × G)) := do
  let (mapped, f) ← mapFn.call_mut state.1 input.2
  let (acc, g) ← foldFn.call_mut state.2 (input.1, mapped)
  ok (acc, (f, g))

def IteratorPrototype.mapFoldFn {Item B Acc F G : Type}
    (mapFn : core.ops.function.FnMut F Item B)
    (foldFn : core.ops.function.FnMut G (Acc × B) Acc) :
    core.ops.function.FnMut (F × G) (Acc × Item) Acc where
  FnOnceInst := { call_once := fun state input => do
    let (acc, _) ← mapFoldCall mapFn foldFn state input
    ok acc }
  call_mut := mapFoldCall mapFn foldFn

/-- Rust's override delegates to the underlying iterator's actual `fold`;
this preserves overrides rather than replacing them with a `next` loop. -/
@[rust_fun "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::fold"]
def core.iter.adapters.map.Map.fold {I Item B F Acc G : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (mapFn : core.ops.function.FnMut F Item B)
    (foldFn : core.ops.function.FnMut G (Acc × B) Acc)
    (self : core.iter.adapters.map.Map I F) (acc : Acc) (g : G) : Result Acc :=
  iter.fold (IteratorPrototype.mapFoldFn mapFn foldFn) self.iter acc (self.f, g)

@[rust_trait_impl "core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>"]
def core.iter.traits.iterator.IteratorMap {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (fn : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B where
  next := core.iter.adapters.map.Map.next iter fn
  fold := core.iter.adapters.map.Map.fold iter fn

namespace IteratorPrototype

theorem map_next_none {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item) (fn : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) (source : I)
    (h : iter.next self.iter = ok (none, source)) :
    core.iter.adapters.map.Map.next iter fn self = ok (none, ⟨source, self.f⟩) := by
  simp only [core.iter.adapters.map.Map.next, h, bind_tc_eq, Aeneas.Std.bind_ok]

theorem map_next_some {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item) (fn : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) (source : I) (item : Item) (value : B) (state : F)
    (hnext : iter.next self.iter = ok (some item, source))
    (hcall : fn.call_mut self.f item = ok (value, state)) :
    core.iter.adapters.map.Map.next iter fn self = ok (some value, ⟨source, state⟩) := by
  simp only [core.iter.adapters.map.Map.next, hnext, hcall, bind_tc_eq, Aeneas.Std.bind_ok]

theorem map_next_callback_fail {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item) (fn : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) (source : I) (item : Item) (error : Error)
    (hnext : iter.next self.iter = ok (some item, source))
    (hcall : fn.call_mut self.f item = fail error) :
    core.iter.adapters.map.Map.next iter fn self = fail error := by
  simp [core.iter.adapters.map.Map.next, hnext, hcall]

theorem map_next_callback_div {I Item B F : Type}
    (iter : core.iter.traits.iterator.Iterator I Item) (fn : core.ops.function.FnMut F Item B)
    (self : core.iter.adapters.map.Map I F) (source : I) (item : Item)
    (hnext : iter.next self.iter = ok (some item, source))
    (hcall : fn.call_mut self.f item = div) :
    core.iter.adapters.map.Map.next iter fn self = div := by
  simp [core.iter.adapters.map.Map.next, hnext, hcall]

theorem map_fold_native {I Item B F Acc G : Type}
    (iter : core.iter.traits.iterator.Iterator I Item)
    (mapFn : core.ops.function.FnMut F Item B)
    (foldFn : core.ops.function.FnMut G (Acc × B) Acc)
    (self : core.iter.adapters.map.Map I F) (acc : Acc) (g : G) :
    core.iter.adapters.map.Map.fold iter mapFn foldFn self acc g =
      iter.fold (mapFoldFn mapFn foldFn) self.iter acc (self.f, g) := rfl

end IteratorPrototype
end Aeneas.Std
