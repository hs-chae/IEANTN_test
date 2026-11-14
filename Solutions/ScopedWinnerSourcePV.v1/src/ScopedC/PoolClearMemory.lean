/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolKeepCanonical
import ScopedC.PoolTokens

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure MarkContext (l : PoolLayout) (s : State) (i mark : Nat) : Prop where
  local_mark : s.env.lookup "mark" = some ⟨i,0,[]⟩
  read_mark : s.heap[i]? = some {type:="unsigned int",cells:=[some (word mark)]}
  ne_top : i ≠ l.top

 theorem mark_store_top {l : PoolLayout} {s : State} {i mark top : Nat}
    (h : MarkContext l s i mark) : MarkContext l (storeTop l s top) i mark := by
  exact ⟨h.local_mark,by simpa [storeTop,storeObject,h.ne_top,Ne.symm h.ne_top] using h.read_mark,h.ne_top⟩
 theorem mark_nats {l : PoolLayout} {s : State} {i mark : Nat}
    (h : MarkContext l s i mark) (a : NatArena.Arena) :
    MarkContext l {s with nats:=a} i mark := ⟨h.local_mark,h.read_mark,h.ne_top⟩
 theorem eval_mark {l : PoolLayout} {s : State} {i mark fuel : Nat} (call : Call)
    (h : MarkContext l s i mark) :
    evalExpr Header.layout call (fuel+1) s (.var "mark") = some (word mark,s) := by
  rw [evalExpr]
  simp [getVar,h.local_mark,h.read_mark,Machine.read,nested,initialized,word]

 /-- The active pool references, in the descending order used by clearTo.
 Entries beyond the active prefix are deliberately unrestricted. -/
 def PoolEntries (cells : List (Option Value)) (refs : List Nat) : Prop :=
  ∀ i, i < refs.length → cells[i]? =
    (refs.reverse[i]?).map (fun slot => some (Value.natObject slot))

 theorem entries_head {cells : List (Option Value)} {first : Nat} {rest : List Nat}
    (h : PoolEntries cells (first::rest)) :
    cells[rest.length]? = some (some (.natObject first)) := by
  have hh := h rest.length (by simp)
  simpa [List.reverse_cons,List.getElem?_append] using hh

 theorem entries_tail {cells : List (Option Value)} {first : Nat} {rest : List Nat}
    (h : PoolEntries cells (first::rest)) : PoolEntries cells rest := by
  intro i hi
  have hh := h i (by simp;omega)
  rw [List.reverse_cons,List.getElem?_append_left (by simpa using hi)] at hh
  exact hh

 theorem eval_pool_index {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (ht : top < capacity)
    (cell : cells[top]? = some (some (.natObject slot))) :
    evalExpr Header.layout call (fuel+3) s (.index (.var "pool") (.var "poolTop")) =
      some (.natObject slot,s) := by
  rw [evalExpr,lvalue_pool_top call h free ht]
  simp [Machine.read,h.pool_read,poolObject,cell,nested,initialized]

 theorem eval_decrement {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (hp : 0 < top) :
    Eval Header.layout call (.binary "=" (.var "poolTop") (.binary "-" (.var "poolTop") (.nat 1)))
      s (storeTop l s (top-1)) (word (top-1)) := by
  have hn : top-1 < 2^32 := by have := h.top_range;omega
  refine ⟨5,?_⟩
  have rhs : evalExpr Header.layout call 4 s (.binary "-" (.var "poolTop") (.nat 1)) =
      some (word (top-1),s) := by
    have hc : evalExpr Header.layout call 3 s (.nat 1) = some (.integer ⟨⟨true,32⟩,1⟩,s) := rfl
    exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (eval_top call h free) hc (binary_sub_one s top hp h.top_range)
  exact eval_assign call rhs (lvalue_top call h free) (write_counter h.top_read hn)

 theorem eval_clear_guard {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mark i : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (hm : MarkContext l s i mark) (hmark : mark ≤ top) :
    Eval Header.layout call (.binary ">" (.var "poolTop") (.var "mark")) s s
      (boolean Header.layout (decide (top > mark))) := by
  refine ⟨4,?_⟩
  exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (eval_top call h free) (eval_mark call hm)
    (binary_gt s top mark h.top_range (by have := h.top_range;omega))

 theorem eval_bad_mark_guard {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mark i : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (hm : MarkContext l s i mark) (hmark : mark ≤ top) :
    Eval Header.layout call (.binary ">" (.var "mark") (.var "poolTop")) s s
      (boolean Header.layout false) := by
  have hfalse : decide (mark > top) = false := by simp;omega
  refine ⟨4,?_⟩
  rw [← hfalse]
  exact eval_binary_plain call (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (eval_mark call hm) (eval_top call h free)
    (binary_gt s mark top (by have := h.top_range;omega) h.top_range)

 theorem runtime_release {s : State} {slot : Nat} {after : NatArena.Arena}
    (run : NatArena.release s.nats slot = some after) :
    RuntimeCore.call "lean_dec" [.natObject slot] s = some (.unit,{s with nats:=after}) := by
  simp [RuntimeCore.call,RuntimeCore.binaryName,run]

 theorem release_clear_eq {a after : NatArena.Arena} {slot : Nat}
    (run : NatArena.release a slot = some after) (refs : List Nat) :
    NatArena.clear after refs = NatArena.clear a (slot::refs) := by
  unfold NatArena.release at run
  split at run
  · cases Option.some.inj run
    apply congrArg (NatArena.Arena.mk a.values)
    funext i
    change (if i = slot then a.owners i-1 else a.owners i)-refs.count i = a.owners i-(slot::refs).count i
    by_cases hi : i = slot
    · subst i
      simp only [↓reduceIte,List.count_cons_self]
      omega
    · simp [hi,Ne.symm hi]
  · contradiction

 theorem store_top_same {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) : storeTop l s top = s := by
  obtain ⟨ht,he⟩ := List.getElem?_eq_some_iff.mp h.top_read
  have hset : s.heap.set l.top (counterObject top) = s.heap := by
    rw [← he]
    exact List.set_getElem_self ht
  simp [storeTop,storeObject,hset]

end ScopedC.PoolCalls
