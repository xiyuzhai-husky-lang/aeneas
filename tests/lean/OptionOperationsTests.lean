module
public import OptionOperations
@[expose] public section
open Aeneas Aeneas.Std
namespace option_operations.tests

theorem map_none {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (f : F) : map fnOnce none f = .ok none := rfl

theorem map_some {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (x : T) (f : F) : map fnOnce (some x) f =
      (do let y ← fnOnce.call_once f x; .ok (some y)) := rfl

theorem map_eq {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (self : Option T) (f : F) (g : T → U)
    (hcall : ∀ x, x ∈ self → fnOnce.call_once f x = .ok (g x)) :
    map fnOnce self f = .ok (self.map g) := core.option.Option.map_eq fnOnce self f g hcall

theorem map_or_none {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (default : U) (f : F) : map_or fnOnce none default f = .ok default := rfl

theorem map_or_some {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (x : T) (default : U) (f : F) :
    map_or fnOnce (some x) default f = fnOnce.call_once f x := rfl

theorem cloned_none {T : Type} (cloneInst : core.clone.Clone T) :
    cloned cloneInst none = .ok none := rfl

theorem cloned_eq {T : Type} (cloneInst : core.clone.Clone T) (self : Option T)
    (g : T → T) (hclone : ∀ x, x ∈ self → cloneInst.clone x = .ok (g x)) :
    cloned cloneInst self = .ok (self.map g) := core.option.Option.cloned_eq cloneInst self g hclone

theorem phantom_eq (T : Type) : phantom T = .ok () := rfl

#print axioms map_none
#print axioms map_some
#print axioms map_eq
#print axioms map_or_none
#print axioms map_or_some
#print axioms cloned_none
#print axioms cloned_eq
#print axioms phantom_eq
#print axioms core.option.Option.map_none
#print axioms core.option.Option.map_some
#print axioms core.option.Option.map_eq
#print axioms core.option.Option.map_or_none
#print axioms core.option.Option.map_or_some
#print axioms core.option.Option.cloned_none
#print axioms core.option.Option.cloned_eq
#print axioms Aeneas.Std.core.marker.phantomDataDefault_eq
end option_operations.tests
