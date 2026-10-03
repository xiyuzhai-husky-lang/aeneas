module
public import Aeneas.Std.Core

@[expose] public section
namespace Aeneas.Std.core.option
open Aeneas.Std Aeneas.Std.Result

@[rust_fun "core::option::{core::option::Option<@T>}::map"]
def Option.map {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (self : _root_.Option T) (f : F) : Result (_root_.Option U) :=
  match self with
  | none => .ok none
  | some x => do
    let y ← fnOnce.call_once f x
    .ok (some y)

@[simp] theorem Option.map_none {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (f : F) : Option.map fnOnce none f = .ok none := rfl

theorem Option.map_some {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (x : T) (f : F) : Option.map fnOnce (some x) f =
      (do let y ← fnOnce.call_once f x; .ok (some y)) := rfl

theorem Option.map_eq {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (self : _root_.Option T) (f : F) (g : T → U)
    (hcall : ∀ x, x ∈ self → fnOnce.call_once f x = .ok (g x)) :
    Option.map fnOnce self f = .ok (self.map g) := by
  cases self with
  | none => rfl
  | some x => simp [Option.map, hcall x (by simp)]

@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def Option.map_or {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (self : _root_.Option T) (default : U) (f : F) : Result U :=
  match self with
  | none => .ok default
  | some x => fnOnce.call_once f x

@[simp] theorem Option.map_or_none {T U F : Type}
    (fnOnce : core.ops.function.FnOnce F T U) (default : U) (f : F) :
    Option.map_or fnOnce none default f = .ok default := rfl

@[simp] theorem Option.map_or_some {T U F : Type}
    (fnOnce : core.ops.function.FnOnce F T U) (x : T) (default : U) (f : F) :
    Option.map_or fnOnce (some x) default f = fnOnce.call_once f x := rfl

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def Option.cloned {T : Type} (cloneInst : core.clone.Clone T)
    (self : _root_.Option T) : Result (_root_.Option T) :=
  match self with
  | none => .ok none
  | some x => do
    let y ← cloneInst.clone x
    .ok (some y)

@[simp] theorem Option.cloned_none {T : Type} (cloneInst : core.clone.Clone T) :
    Option.cloned cloneInst none = .ok none := rfl

theorem Option.cloned_eq {T : Type} (cloneInst : core.clone.Clone T)
    (self : _root_.Option T) (g : T → T)
    (hclone : ∀ x, x ∈ self → cloneInst.clone x = .ok (g x)) :
    Option.cloned cloneInst self = .ok (self.map g) := by
  cases self with
  | none => rfl
  | some x => simp [Option.cloned, hclone x (by simp)]

end Aeneas.Std.core.option
