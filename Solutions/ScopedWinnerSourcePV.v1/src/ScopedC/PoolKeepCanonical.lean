/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolCalls

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 theorem frame_store (s : State) (i slot : Nat) (o : Object) (hi : i < s.heap.length) :
    keepFrame (storeObject s i o) slot = storeObject (keepFrame s slot) i o := by
  simp [keepFrame,storeObject,allocate,List.set_append_left i o hi]

 theorem keep_result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) :
    keepResult l (keepFrame s slot) cells top high slot =
      keepFrame (keepResult l s cells top high slot) slot := by
  have hp := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  have hh := (List.getElem?_eq_some_iff.mp h.high_read).choose
  have hs : keepStored l (keepFrame s slot) cells top slot =
      keepFrame (keepStored l s cells top slot) slot := (frame_store s l.pool slot _ hp).symm
  have ht' : l.top < (keepStored l s cells top slot).heap.length := by
    simpa [keepStored,storePool,storeObject] using ht
  have hb : keepStepped l (keepFrame s slot) cells top slot =
      keepFrame (keepStepped l s cells top slot) slot := by
    unfold keepStepped
    rw [hs]
    exact (frame_store _ l.top slot _ ht').symm
  have hh' : l.high < (keepStepped l s cells top slot).heap.length := by
    simpa [keepStepped,keepStored,storeTop,storePool,storeObject] using hh
  unfold keepResult
  split
  · rw [hb]
    exact (frame_store _ l.high slot _ hh').symm
  · exact hb

 theorem pop_keep_frame {s t : State} (slot : Nat)
    (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s (keepFrame t slot) = t := by
  cases t
  simp_all [popScope,keepFrame,allocate]

 theorem keep_call_canonical {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot value : Nat} (h : GenericPoolContext l s cells top high)
    (ht : top < capacity) (borrow : NatArena.Borrow s.nats slot value) :
    SourceCall Header.layout Generated.functions 1 "keep" [.natObject slot] s (.natObject slot)
      (keepResult l s cells top high slot) := by
  have old := keep_call h ht borrow
  rw [keep_result_frame h,pop_keep_frame slot (keep_result_shape l s cells top high slot).1
    (keep_result_shape l s cells top high slot).2.1] at old
  exact old

end ScopedC.PoolCalls
