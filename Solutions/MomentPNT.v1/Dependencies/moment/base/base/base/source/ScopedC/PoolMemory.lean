/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PrimitiveCalls

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capacity : Nat := 4000000
def word (n : Nat) : Value := .integer ⟨⟨false,32⟩,(n:Int)⟩
def poolObject (cells : List (Option Value)) : Object :=
  {type:="N",cells:=cells,isArray:=true,writable:=true}
def counterObject (n : Nat) : Object := {type:="unsigned",cells:=[some (word n)]}

structure PoolLayout where
  pool : Nat
  top : Nat
  high : Nat
  pool_ne_top : pool ≠ top
  pool_ne_high : pool ≠ high
  top_ne_high : top ≠ high

/-- Actual globals and allocated cells, independent of a successful execution
or any desired evaluator result. Local parameter frames are separate. -/
structure GenericPoolContext (l : PoolLayout) (s : State)
    (cells : List (Option Value)) (top high : Nat) : Prop where
  global_pool : s.globals.lookup "pool" = some ⟨l.pool,0,[]⟩
  global_top : s.globals.lookup "poolTop" = some ⟨l.top,0,[]⟩
  global_high : s.globals.lookup "poolHigh" = some ⟨l.high,0,[]⟩
  pool_read : s.heap[l.pool]? = some (poolObject cells)
  top_read : s.heap[l.top]? = some (counterObject top)
  high_read : s.heap[l.high]? = some (counterObject high)
  extent : cells.length = capacity
  high_range : high < 2^32
  top_range : top < 2^32

def LocalsFree (s : State) : Prop :=
  s.env.lookup "pool" = none ∧ s.env.lookup "poolTop" = none ∧
    s.env.lookup "poolHigh" = none

def storeObject (s : State) (i : Nat) (o : Object) : State :=
  {s with heap:=s.heap.set i o}
def storePool (l : PoolLayout) (s : State) (cells : List (Option Value)) : State :=
  storeObject s l.pool (poolObject cells)
def storeTop (l : PoolLayout) (s : State) (top : Nat) : State :=
  storeObject s l.top (counterObject top)
def storeHigh (l : PoolLayout) (s : State) (high : Nat) : State :=
  storeObject s l.high (counterObject high)

 theorem cast_unsigned (s : State) (n : Nat) (hn : n < 2^32) :
    castValue Header.layout s 100 "unsigned" (word n) = some (word n) := by
  have range : Scalar.InRange ⟨false,32⟩ (n:Int) := by
    simp only [Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,Bool.false_eq_true,↓reduceIte]
    constructor
    · omega
    · constructor
      · exact_mod_cast Nat.zero_le n
      · exact_mod_cast hn
  change (do let x ← Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(n:Int)⟩
             pure (Value.integer x)) = some (word n)
  simp only [Scalar.cast]
  rw [Scalar.make_exact range]
  rfl

 theorem write_counter {s : State} {i old n : Nat}
    (read : s.heap[i]? = some (counterObject old)) (hn : n < 2^32) :
    write Header.layout s ⟨i,0,[]⟩ true (word n) =
      some (word n,storeObject s i (counterObject n)) := by
  simp [write,addressType,typeAt,read,counterObject,cast_unsigned s n hn,storeObject]


 theorem write_pool {s : State} {i index slot value : Nat} {cells : List (Option Value)}
    (read : s.heap[i]? = some (poolObject cells)) (index_ok : index < cells.length)
    (borrow : NatArena.Borrow s.nats slot value) :
    write Header.layout s ⟨i,index,[]⟩ true (.natObject slot) =
      some (.natObject slot,storeObject s i (poolObject (cells.set index (some (.natObject slot))))) := by
  have cell : cells[index]? = some cells[index] := List.getElem?_eq_getElem index_ok
  simp [write,addressType,typeAt,read,poolObject,index_ok,PrimitiveCalls.cast_N borrow,
    cell,storeObject]


 theorem locals_store (l : PoolLayout) (s : State) (i : Nat) (o : Object)
    (h : LocalsFree s) : LocalsFree (storeObject s i o) := h

 theorem context_store_pool {l : PoolLayout} {s : State} {cells fresh : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high)
    (extent : fresh.length = capacity) :
    GenericPoolContext l (storePool l s fresh) fresh top high := by
  have hp : l.pool < s.heap.length := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  constructor
  · exact h.global_pool
  · exact h.global_top
  · exact h.global_high
  · simp [storePool,storeObject,hp]
  · simpa [storePool,storeObject,l.pool_ne_top,Ne.symm l.pool_ne_top] using h.top_read
  · simpa [storePool,storeObject,l.pool_ne_high,Ne.symm l.pool_ne_high] using h.high_read
  · exact extent
  · exact h.high_range
  · exact h.top_range

 theorem context_store_top {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fresh : Nat} (h : GenericPoolContext l s cells top high) (range : fresh < 2^32) :
    GenericPoolContext l (storeTop l s fresh) cells fresh high := by
  have ht : l.top < s.heap.length := (List.getElem?_eq_some_iff.mp h.top_read).choose
  constructor
  · exact h.global_pool
  · exact h.global_top
  · exact h.global_high
  · simpa [storeTop,storeObject,l.pool_ne_top,Ne.symm l.pool_ne_top] using h.pool_read
  · simp [storeTop,storeObject,ht]
  · simpa [storeTop,storeObject,l.top_ne_high,Ne.symm l.top_ne_high] using h.high_read
  · exact h.extent
  · exact h.high_range
  · exact range

 theorem context_store_high {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fresh : Nat} (h : GenericPoolContext l s cells top high)
    (range : fresh < 2^32) (le_high : top ≤ fresh) :
    GenericPoolContext l (storeHigh l s fresh) cells top fresh := by
  have hh : l.high < s.heap.length := (List.getElem?_eq_some_iff.mp h.high_read).choose
  constructor
  · exact h.global_pool
  · exact h.global_top
  · exact h.global_high
  · simpa [storeHigh,storeObject,l.pool_ne_high,Ne.symm l.pool_ne_high] using h.pool_read
  · simpa [storeHigh,storeObject,l.top_ne_high,Ne.symm l.top_ne_high] using h.top_read
  · simp [storeHigh,storeObject,hh]
  · exact h.extent
  · exact range
  · exact h.top_range

end ScopedC.PoolCalls
