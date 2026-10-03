import Aeneas
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.WP
namespace iterator_ops.tests

/-- Exhausted map never calls the mutable closure. -/
theorem map_none {I F T B : Type} (iter : core.iter.traits.iterator.Iterator I T)
    (call : core.ops.function.FnMut F T B) (s next : I) (f : F)
    (h : iter.next s = .ok (none, next)) :
    core.iter.adapters.map.IteratorMap.next iter call ⟨s, f⟩ = .ok (none, ⟨next, f⟩) := by
  simp only [core.iter.adapters.map.IteratorMap.next, h, bind_tc_ok]

/-- A successful map step retains both the updated iterator and callback state. -/
theorem map_some {I F T B : Type} (iter : core.iter.traits.iterator.Iterator I T)
    (call : core.ops.function.FnMut F T B) (s next : I) (f f' : F) (x : T) (y : B)
    (hi : iter.next s = .ok (some x, next)) (hc : call.call_mut f x = .ok (y, f')) :
    core.iter.adapters.map.IteratorMap.next iter call ⟨s, f⟩ = .ok (some y, ⟨next, f'⟩) := by
  simp only [core.iter.adapters.map.IteratorMap.next, hi, hc, bind_tc_ok]

theorem repeat_next {T : Type} (clone : core.clone.Clone T) (x : T)
    (hc : clone.clone x = .ok x) :
    core.iter.sources.repeat.IteratorRepeat.next clone ⟨x⟩ = .ok (some x, ⟨x⟩) := by
  simp only [core.iter.sources.repeat.IteratorRepeat.next, hc, bind_tc_ok]

theorem vec_default (T : Type) :
    alloc.vec.VecDefault.default T = .ok (alloc.vec.Vec.new T) := rfl

theorem vec_reserve {T : Type} (v : alloc.vec.Vec T) (n : Usize)
    (h : v.val.length + n.val ≤ Usize.max) : alloc.vec.Vec.reserve v n = .ok v := by
  simp only [alloc.vec.Vec.reserve, h, ite_true]

theorem vec_extend_finite {T I : Type} (iter : core.iter.traits.iterator.Iterator I T)
    {s : I} {xs : List T} (ht : IteratorTrace iter s xs) (v : alloc.vec.Vec T)
    (hroom : v.val.length + xs.length ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extendIterator iter v s = .ok w ∧ w.val = v.val ++ xs := alloc.vec.Vec.extend_finite iter ht v hroom
theorem take_repeat_trace_aux {T : Type} (clone : core.clone.Clone T) (x : T)
    (hc : clone.clone x = .ok x) (fuel : Nat) :
    ∀ n : Usize, n.val = fuel → IteratorTrace
      (core.iter.traits.iterator.IteratorTake (core.iter.traits.iterator.IteratorRepeat clone))
      ⟨⟨x⟩, n⟩ (List.replicate n.val x) := IteratorTrace.take_repeat_aux clone x hc fuel
theorem vec_extend_repeat_take {T : Type} (clone : core.clone.Clone T) (x : T)
    (hc : clone.clone x = .ok x) (n : Usize) (v : alloc.vec.Vec T)
    (hroom : v.val.length + n.val ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extend
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.traits.iterator.IteratorTake (core.iter.traits.iterator.IteratorRepeat clone)))
      v ⟨⟨x⟩, n⟩ = .ok w ∧ w.val = v.val ++ List.replicate n.val x := alloc.vec.Vec.extend_repeat_take clone x hc n v hroom

#print axioms map_none
#print axioms map_some
#print axioms repeat_next
#print axioms vec_default
#print axioms vec_reserve
#print axioms vec_extend_finite
#print axioms take_repeat_trace_aux
#print axioms vec_extend_repeat_take

end iterator_ops.tests
