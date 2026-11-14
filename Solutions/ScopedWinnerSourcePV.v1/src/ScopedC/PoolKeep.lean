/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolBinaryEval
import ScopedC.Generated

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure XContext (l : PoolLayout) (s : State) (i slot : Nat) : Prop where
  local_x : s.env.lookup "x" = some ⟨i,0,[]⟩
  read_x : s.heap[i]? = some {type:="N",cells:=[some (.natObject slot)]}
  ne_pool : i ≠ l.pool
  ne_top : i ≠ l.top
  ne_high : i ≠ l.high

 theorem x_store {l : PoolLayout} {s : State} {i slot j : Nat} (o : Object)
    (h : XContext l s i slot) (hj : j ≠ i) : XContext l (storeObject s j o) i slot := by
  exact ⟨h.local_x,by simpa [storeObject,hj,Ne.symm hj] using h.read_x,h.ne_pool,h.ne_top,h.ne_high⟩

 theorem eval_x {l : PoolLayout} {s : State} {i slot fuel : Nat} (call : Call)
    (h : XContext l s i slot) :
    evalExpr Header.layout call (fuel+1) s (.var "x") = some (.natObject slot,s) := by
  rw [evalExpr]
  simp [getVar,h.local_x,h.read_x,Machine.read,nested,initialized]

 def keepStored (l : PoolLayout) (s : State) (cells : List (Option Value)) (top slot : Nat) : State :=
  storePool l s (cells.set top (some (.natObject slot)))
 def keepStepped (l : PoolLayout) (s : State) (cells : List (Option Value)) (top slot : Nat) : State :=
  storeTop l (keepStored l s cells top slot) (top+1)
 def keepResult (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high slot : Nat) : State :=
  if high < top+1 then storeHigh l (keepStepped l s cells top slot) (top+1)
  else keepStepped l s cells top slot

 theorem keep_stored_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) :
    GenericPoolContext l (keepStored l s cells top slot)
      (cells.set top (some (.natObject slot))) top high := by
  exact context_store_pool h (by simpa using h.extent)

 theorem keep_stepped_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) (ht : top < capacity) :
    GenericPoolContext l (keepStepped l s cells top slot)
      (cells.set top (some (.natObject slot))) (top+1) high := by
  exact context_store_top (keep_stored_context h) (by dsimp [capacity] at ht;omega)

 theorem keep_result_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} (h : GenericPoolContext l s cells top high) (ht : top < capacity) :
    GenericPoolContext l (keepResult l s cells top high slot)
      (cells.set top (some (.natObject slot))) (top+1) (Max.max high (top+1)) := by
  have hb := keep_stepped_context (slot:=slot) h ht
  by_cases hh : high < top+1
  · simpa only [keepResult,hh,↓reduceIte,max_eq_right hh.le] using
      context_store_high hb (by dsimp [capacity] at ht;omega) le_rfl
  · simpa only [keepResult,hh,↓reduceIte,max_eq_left (le_of_not_gt hh)] using hb

 theorem keep_result_x {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot i : Nat} (h : XContext l s i slot) :
    XContext l (keepResult l s cells top high slot) i slot := by
  have hs := x_store (poolObject (cells.set top (some (.natObject slot)))) h (Ne.symm h.ne_pool)
  have ht := x_store (counterObject (top+1)) hs (Ne.symm h.ne_top)
  by_cases hh : high < top+1
  · simpa only [keepResult,keepStepped,keepStored,storeHigh,storeTop,storePool,hh,↓reduceIte] using x_store (counterObject (top+1)) ht (Ne.symm h.ne_high)
  · simpa only [keepResult,keepStepped,keepStored,storeHigh,storeTop,storePool,hh,↓reduceIte] using ht

 theorem keep_result_nats (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high slot : Nat) :
    (keepResult l s cells top high slot).nats = s.nats := by
  simp only [keepResult,keepStepped,keepStored,storeTop,storeHigh,storePool,storeObject]
  split <;> rfl

 theorem eval_cap_guard {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (ht : top < capacity) :
    Eval Header.layout call (.binary ">=" (.var "poolTop") (.nat 4000000)) s s
      (boolean Header.layout false) := by
  refine ⟨4,?_⟩
  have hc : evalExpr Header.layout call 3 s (.nat 4000000) =
      some (.integer ⟨⟨true,32⟩,4000000⟩,s) := by rfl
  exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (eval_top call h free) hc (binary_cap s top ht)

 theorem eval_keep_store {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot value i : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (hx : XContext l s i slot) (ht : top < capacity)
    (borrow : NatArena.Borrow s.nats slot value) :
    Eval Header.layout call (.binary "=" (.index (.var "pool") (.var "poolTop")) (.var "x"))
      s (keepStored l s cells top slot) (.natObject slot) := by
  refine ⟨5,?_⟩
  apply eval_assign call (eval_x call hx) (lvalue_pool_top call h free ht)
  exact write_pool h.pool_read (by rw [h.extent];exact ht) borrow

 theorem eval_increment {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (ht : top < capacity) :
    Eval Header.layout call (.binary "=" (.var "poolTop") (.binary "+" (.var "poolTop") (.nat 1)))
      s (storeTop l s (top+1)) (word (top+1)) := by
  have hn : top+1 < 2^32 := by dsimp [capacity] at ht;omega
  refine ⟨5,?_⟩
  have rhs : evalExpr Header.layout call 4 s (.binary "+" (.var "poolTop") (.nat 1)) =
      some (word (top+1),s) := by
    have hc : evalExpr Header.layout call 3 s (.nat 1) = some (.integer ⟨⟨true,32⟩,1⟩,s) := rfl
    exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (eval_top call h free) hc (binary_add_one s top hn)
  exact eval_assign call rhs (lvalue_top call h free) (write_counter h.top_read hn)

 theorem eval_high_guard {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    Eval Header.layout call (.binary "<" (.var "poolHigh") (.var "poolTop")) s s
      (boolean Header.layout (decide (high < top))) := by
  refine ⟨4,?_⟩
  exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (eval_high call h free) (eval_top call h free)
    (binary_lt s high top h.high_range h.top_range)

 theorem eval_update_high {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    Eval Header.layout call (.binary "=" (.var "poolHigh") (.var "poolTop")) s
      (storeHigh l s top) (word top) := by
  refine ⟨4,?_⟩
  exact eval_assign call (eval_top call h free) (lvalue_high call h free)
    (write_counter h.high_read h.top_range)

end ScopedC.PoolCalls
