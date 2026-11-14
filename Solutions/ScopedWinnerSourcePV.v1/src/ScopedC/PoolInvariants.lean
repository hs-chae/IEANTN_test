/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolClearCalls
import ScopedC.PoolOwnership

namespace ScopedC.PoolCalls
open ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem entries_drop {cells : List (Option Value)} {refs : List Nat} (k : Nat)
    (entries : PoolEntries cells refs) : PoolEntries cells (refs.drop k) := by
  intro i hi
  have hlen : i < refs.length-k := by simpa using hi
  have hidx : i < refs.length := by omega
  rw [List.reverse_drop,List.getElem?_take_of_lt hlen]
  exact entries i hidx

 theorem owned_clear_drop {a : NatArena.Arena} {refs : List Nat} (k : Nat)
    (owned : NatArena.PoolOwned a refs) :
    NatArena.PoolOwned (NatArena.clear a (refs.take k)) (refs.drop k) := by
  intro i
  have h := owned i
  have count : refs.count i = (refs.take k).count i + (refs.drop k).count i := by
    conv_lhs => rw [← List.take_append_drop k refs]
    rw [List.count_append]
  change (refs.drop k).count i ≤ a.owners i-(refs.take k).count i
  omega

 theorem valid_clear_drop {a : NatArena.Arena} {refs : List Nat} (k : Nat)
    (valid : RefsValid a refs) : RefsValid (NatArena.clear a (refs.take k)) (refs.drop k) := by
  intro i hi
  exact valid i (List.mem_of_mem_drop hi)

 theorem clear_result_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mark : Nat} (h : GenericPoolContext l s cells top high)
    (hmark : mark ≤ top) (released : List Nat) :
    GenericPoolContext l (clearResult l s mark released) cells mark high := by
  exact context_nats (context_store_top h (by have := h.top_range;omega)) _

 theorem clear_retained_borrow {l : PoolLayout} {s : State} {released : List Nat}
    {slot value mark : Nat} (valueAt : s.nats.values[slot]? = some value)
    (retained : released.count slot < s.nats.owners slot) :
    NatArena.Borrow (clearResult l s mark released).nats slot value :=
  NatArena.retained_token_survives_clear valueAt retained

 /-- Closed source call with the actual pool invariant re-established at mark.
 The inactive memory still contains old pointers, which are never read by this
 invariant or the next clearTo loop. -/
 theorem clear_call_with_invariant {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {refs : List Nat} {high mark : Nat}
    (h : GenericPoolContext l s cells refs.length high) (hmark : mark ≤ refs.length)
    (hc : refs.length ≤ capacity) (entries : PoolEntries cells refs)
    (valid : RefsValid s.nats refs) (owned : NatArena.PoolOwned s.nats refs) :
    let after := clearResult l s mark (refs.take (refs.length-mark))
    let kept := refs.drop (refs.length-mark)
    SourceCall Header.layout Generated.functions 1 "clearTo" [word mark] s .unit after ∧
    GenericPoolContext l after cells mark high ∧ kept.length = mark ∧
    PoolEntries cells kept ∧ RefsValid after.nats kept ∧ NatArena.PoolOwned after.nats kept := by
  dsimp
  refine ⟨clear_call_canonical h hmark hc entries valid owned,clear_result_context h hmark _,?_,
    entries_drop _ entries,valid_clear_drop _ valid,owned_clear_drop _ owned⟩
  simp only [List.length_drop]
  omega

 theorem keep_call_with_invariant {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {refs : List Nat} {high slot value : Nat}
    (h : GenericPoolContext l s cells refs.length high) (hc : refs.length < capacity)
    (entries : PoolEntries cells refs) (valid : RefsValid s.nats refs)
    (owned : NatArena.PoolOwned s.nats refs) (borrow : NatArena.Borrow s.nats slot value)
    (spare : refs.count slot < s.nats.owners slot) :
    let after := keepResult l s cells refs.length high slot
    let fresh := cells.set refs.length (some (Value.natObject slot))
    SourceCall Header.layout Generated.functions 1 "keep" [.natObject slot] s (.natObject slot) after ∧
    GenericPoolContext l after fresh (slot::refs).length (Max.max high (slot::refs).length) ∧
    PoolEntries fresh (slot::refs) ∧ RefsValid after.nats (slot::refs) ∧
    NatArena.PoolOwned after.nats (slot::refs) := by
  dsimp
  refine ⟨keep_call_canonical h hc borrow,keep_result_context h hc,
    entries_keep entries (by rw [h.extent];exact hc),?_,?_⟩
  · rw [keep_result_nats]
    exact valid_cons_of_borrow valid borrow
  · rw [keep_result_nats]
    exact owned_cons_of_spare owned spare

end ScopedC.PoolCalls
