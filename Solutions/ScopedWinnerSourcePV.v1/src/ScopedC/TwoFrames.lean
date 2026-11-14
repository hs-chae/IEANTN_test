/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatFrames

namespace ScopedC.TwoFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (type name : String) (v : Value) (secondType secondName : String) (w : Value) : State :=
  allocate (allocate {s with env:=[]} type name (some v)) secondType secondName (some w)

theorem context_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (type name : String) (v : Value) (secondType secondName : String) (w : Value) :
    GenericPoolContext l (frame s type name v secondType secondName w) cells top high := by
  simpa [frame,allocate,List.append_assoc] using
    context_env (context_append (context_env h [])
      [{type:=type,cells:=[some v]},{type:=secondType,cells:=[some w]}])
      [(secondName,⟨s.heap.length+1,0,[]⟩),(name,⟨s.heap.length,0,[]⟩)]

theorem frame_store (s : State) (i : Nat) (o : Object) (hi : i < s.heap.length)
    (type name : String) (v : Value) (secondType secondName : String) (w : Value) :
    frame (storeObject s i o) type name v secondType secondName w = storeObject (frame s type name v secondType secondName w) i o := by
  simp [frame,storeObject,allocate,List.set_append_left i o hi]

theorem result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) (type name : String) (v : Value) (secondType secondName : String) (w : Value) :
    keepResult l (frame s type name v secondType secondName w) cells top high slot =
      frame (keepResult l s cells top high slot) type name v secondType secondName w := by
  have hp := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  have hh := (List.getElem?_eq_some_iff.mp h.high_read).choose
  have hs : keepStored l (frame s type name v secondType secondName w) cells top slot =
      frame (keepStored l s cells top slot) type name v secondType secondName w := (frame_store s l.pool _ hp type name v secondType secondName w).symm
  have ht' : l.top < (keepStored l s cells top slot).heap.length := by
    simpa [keepStored,storePool,storeObject] using ht
  have hb : keepStepped l (frame s type name v secondType secondName w) cells top slot =
      frame (keepStepped l s cells top slot) type name v secondType secondName w := by
    unfold keepStepped
    rw [hs]
    exact (frame_store _ l.top _ ht' type name v secondType secondName w).symm
  have hh' : l.high < (keepStepped l s cells top slot).heap.length := by
    simpa [keepStepped,keepStored,storeTop,storePool,storeObject] using hh
  unfold keepResult
  split
  · rw [hb]
    exact (frame_store _ l.high _ hh' type name v secondType secondName w).symm
  · exact hb

theorem pop_frame {s t : State} (type name : String) (v : Value) (secondType secondName : String) (w : Value)
    (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s (frame t type name v secondType secondName w) = t := by
  cases t
  simp_all [popScope,frame,allocate]

end ScopedC.TwoFrames
