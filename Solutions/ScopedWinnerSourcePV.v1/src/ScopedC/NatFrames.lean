/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolModel
import ScopedC.ExpressionTemplates

namespace ScopedC.NatFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem context_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (a b : Nat) :
    GenericPoolContext l (PrimitiveCalls.frame s a b) cells top high := by
  simpa [PrimitiveCalls.frame,allocate,List.append_assoc] using context_env (context_append (context_env h [])
    [{type:="N",cells:=[some (.natObject a)]},{type:="N",cells:=[some (.natObject b)]}])
    [("b",⟨s.heap.length+1,0,[]⟩),("a",⟨s.heap.length,0,[]⟩)]

theorem frame_store (s : State) (i a b : Nat) (o : Object) (hi : i < s.heap.length) :
    PrimitiveCalls.frame (storeObject s i o) a b =
      storeObject (PrimitiveCalls.frame s a b) i o := by
  simp [PrimitiveCalls.frame,storeObject,allocate,List.set_append_left i o hi]

theorem result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot a b : Nat} (h : GenericPoolContext l s cells top high) :
    keepResult l (PrimitiveCalls.frame s a b) cells top high slot =
      PrimitiveCalls.frame (keepResult l s cells top high slot) a b := by
  have hp := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  have hh := (List.getElem?_eq_some_iff.mp h.high_read).choose
  have hs : keepStored l (PrimitiveCalls.frame s a b) cells top slot =
      PrimitiveCalls.frame (keepStored l s cells top slot) a b := (frame_store s l.pool a b _ hp).symm
  have ht' : l.top < (keepStored l s cells top slot).heap.length := by
    simpa [keepStored,storePool,storeObject] using ht
  have hb : keepStepped l (PrimitiveCalls.frame s a b) cells top slot =
      PrimitiveCalls.frame (keepStepped l s cells top slot) a b := by
    unfold keepStepped
    rw [hs]
    exact (frame_store _ l.top a b _ ht').symm
  have hh' : l.high < (keepStepped l s cells top slot).heap.length := by
    simpa [keepStepped,keepStored,storeTop,storePool,storeObject] using hh
  unfold keepResult
  split
  · rw [hb]
    exact (frame_store _ l.high a b _ hh').symm
  · exact hb

theorem pop_frame {s t : State} (a b : Nat)
    (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s (PrimitiveCalls.frame t a b) = t := by
  cases t
  simp_all [popScope,PrimitiveCalls.frame,allocate,List.take_append]

theorem runtime_binary {name : String} {op : NatArena.BinaryOp} {s : State}
    {a b n m result : Nat} (hn : RuntimeCore.binaryName name = some op)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m)
    (hop : NatArena.operation op n m = some result) :
    RuntimeCore.call name [.natObject a,.natObject b] s =
      some (.natObject s.nats.values.length,{s with nats:=(NatArena.allocate s.nats result).2}) := by
  simp [RuntimeCore.call,hn,NatArena.binary,NatArena.read_of_borrow ha,
    NatArena.read_of_borrow hb,hop,NatArena.allocate]

end ScopedC.NatFrames
