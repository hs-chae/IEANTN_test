/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatFrames

namespace ScopedC.OneFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (type name : String) (v : Value) : State :=
  allocate {s with env:=[]} type name (some v)

theorem context_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (type name : String) (v : Value) :
    GenericPoolContext l (frame s type name v) cells top high := by
  exact context_env (context_append (context_env h []) [{type:=type,cells:=[some v]}])
    [(name,⟨s.heap.length,0,[]⟩)]

theorem frame_store (s : State) (i : Nat) (o : Object) (hi : i < s.heap.length)
    (type name : String) (v : Value) :
    frame (storeObject s i o) type name v = storeObject (frame s type name v) i o := by
  simp [frame,storeObject,allocate,List.set_append_left i o hi]

theorem result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) (type name : String) (v : Value) :
    keepResult l (frame s type name v) cells top high slot =
      frame (keepResult l s cells top high slot) type name v := by
  have hp := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  have hh := (List.getElem?_eq_some_iff.mp h.high_read).choose
  have hs : keepStored l (frame s type name v) cells top slot =
      frame (keepStored l s cells top slot) type name v := (frame_store s l.pool _ hp type name v).symm
  have ht' : l.top < (keepStored l s cells top slot).heap.length := by
    simpa [keepStored,storePool,storeObject] using ht
  have hb : keepStepped l (frame s type name v) cells top slot =
      frame (keepStepped l s cells top slot) type name v := by
    unfold keepStepped
    rw [hs]
    exact (frame_store _ l.top _ ht' type name v).symm
  have hh' : l.high < (keepStepped l s cells top slot).heap.length := by
    simpa [keepStepped,keepStored,storeTop,storePool,storeObject] using hh
  unfold keepResult
  split
  · rw [hb]
    exact (frame_store _ l.high _ hh' type name v).symm
  · exact hb

theorem pop_frame {s t : State} (type name : String) (v : Value)
    (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s (frame t type name v) = t := by
  cases t
  simp_all [popScope,frame,allocate]

end ScopedC.OneFrames
