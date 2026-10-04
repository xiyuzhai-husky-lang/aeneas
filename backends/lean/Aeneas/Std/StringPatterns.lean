module
public import Aeneas.Std.StringBytes
public import Aeneas.Std.Core.Result
public section
namespace Aeneas.Std
open Result

/-- Behavioral interface for the prefix operations modeled here. Native Searcher
    construction is outside this subset; it is not replaced by an opaque method. -/
@[rust_trait "core::str::pattern::Pattern"]
structure core.str.pattern.Pattern (Self : Type) where
  prefixBytes : Self → List U8

@[expose, reducible, rust_trait_impl "core::str::pattern::Pattern<char>"]
def core.str.pattern.PatternChar : core.str.pattern.Pattern Char :=
  ⟨fun ch => alloc.string.String.utf8Bytes (String.singleton ch)⟩

@[expose, reducible, rust_trait_impl "core::str::pattern::Pattern<&'b str>"]
def core.str.pattern.PatternStr : core.str.pattern.Pattern Str := ⟨fun s => s.val⟩

@[expose, rust_fun "core::str::{str}::starts_with"]
def core.str.Str.starts_with {P : Type} (pattern : core.str.pattern.Pattern P)
    (source : Str) (needle : P) : Result Bool :=
  ok (decide ((pattern.prefixBytes needle).IsPrefix source.val))

@[expose, rust_fun "core::str::{str}::strip_prefix"]
def core.str.Str.strip_prefix {P : Type} (pattern : core.str.pattern.Pattern P)
    (source : Str) (needle : P) : Result (Option Str) :=
  if (pattern.prefixBytes needle).IsPrefix source.val then
    ok (some (Slice.from (source.val.drop (pattern.prefixBytes needle).length)
      (by exact by rw [List.length_drop]; exact (Nat.sub_le _ _).trans source.property)))
  else ok none

theorem core.str.Str.starts_with_exact {P : Type} (pattern : core.str.pattern.Pattern P)
    (source : Str) (needle : P) :
    starts_with pattern source needle = ok (decide ((pattern.prefixBytes needle).IsPrefix source.val)) := rfl

theorem core.str.Str.strip_prefix_exact {P : Type} (pattern : core.str.pattern.Pattern P)
    (source : Str) (needle : P) (isPrefix : (pattern.prefixBytes needle).IsPrefix source.val) :
    ∃ suffix, strip_prefix pattern source needle = ok (some suffix) ∧
      source.val = pattern.prefixBytes needle ++ suffix.val := by
  refine ⟨Slice.from (source.val.drop (pattern.prefixBytes needle).length)
    (by rw [List.length_drop]; exact (Nat.sub_le _ _).trans source.property),?_,?_⟩
  · simp only [strip_prefix,isPrefix,ite_true]
  · obtain ⟨tail,equality⟩ := isPrefix
    simp only [Slice.from_val]
    rw [← equality]
    simp

end Aeneas.Std
