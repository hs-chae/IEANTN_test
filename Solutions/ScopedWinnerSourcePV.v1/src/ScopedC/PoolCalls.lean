/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolKeep

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

 theorem truth_boolean (b : Bool) : truth (boolean Header.layout b) = b := by
  cases b <;> rfl

 theorem keep_result_shape (l : PoolLayout) (s : State) (cells : List (Option Value)) (top high slot : Nat) :
    (keepResult l s cells top high slot).heap.length = s.heap.length ∧
    (keepResult l s cells top high slot).env = s.env ∧
    (keepResult l s cells top high slot).globals = s.globals := by
  simp only [keepResult,keepStepped,keepStored,storeTop,storeHigh,storePool,storeObject]
  split <;> simp

 theorem pop_same {s t : State} (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s t = t := by
  cases t
  simp_all [popScope]

 theorem keep_body {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot value i : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (hx : XContext l s i slot) (ht : top < capacity)
    (borrow : NatArena.Borrow s.nats slot value) :
    Run Header.layout call Generated.f_keep.body s
      (.returned (keepResult l s cells top high slot) (.natObject slot)) := by
  let a := keepStored l s cells top slot
  let b := keepStepped l s cells top slot
  let final := keepResult l s cells top high slot
  have ha : GenericPoolContext l a (cells.set top (some (.natObject slot))) top high := keep_stored_context h
  have hb : GenericPoolContext l b (cells.set top (some (.natObject slot))) (top+1) high := keep_stepped_context h ht
  have fa : LocalsFree a := free
  have fb : LocalsFree b := free
  have first : Run Header.layout call
      (.branch (.binary ">=" (.var "poolTop") (.nat 4000000)) (.eval (.call (.var "fail") [])) .skip)
      s (.continuing s) := by
    apply Loops.StmtRun.branch (eval_cap_guard call h free ht)
    exact Loops.StmtRun.skip s
  have fourth : Run Header.layout call
      (.branch (.binary "<" (.var "poolHigh") (.var "poolTop"))
        (.eval (.binary "=" (.var "poolHigh") (.var "poolTop"))) .skip)
      b (.continuing final) := by
    apply Loops.StmtRun.branch (eval_high_guard call hb fb)
    rw [truth_boolean]
    by_cases hh : high < top+1
    · simp only [hh,decide_true,↓reduceIte]
      simpa only [final,keepResult,hh,↓reduceIte,b] using
        Loops.StmtRun.evaluate (eval_update_high call hb fb)
    · simp only [hh,decide_false,↓reduceIte]
      simpa only [final,keepResult,hh,↓reduceIte,b,Bool.false_eq_true] using
        (Loops.StmtRun.skip b : Run Header.layout call .skip b (.continuing b))
  have last : Run Header.layout call (.returnStmt (.var "x")) final
      (.returned final (.natObject slot)) :=
    Loops.StmtRun.returnValue ⟨2,eval_x call (keep_result_x hx)⟩
  apply Loops.StmtRun.sequence
    (Loops.SeqRun.next first (Loops.SeqRun.next (Loops.StmtRun.evaluate
      (eval_keep_store call h free hx ht borrow)) (Loops.SeqRun.next
        (Loops.StmtRun.evaluate (eval_increment call ha fa ht))
        (Loops.SeqRun.next fourth (Loops.SeqRun.returned last)))))
  exact ⟨rfl,(pop_same (keep_result_shape l s cells top high slot).1
    (keep_result_shape l s cells top high slot).2.1).symm⟩

 def keepFrame (s : State) (slot : Nat) : State :=
  allocate {s with env:=[]} "N" "x" (some (.natObject slot))

 theorem keep_frame_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (slot : Nat) :
    GenericPoolContext l (keepFrame s slot) cells top high := by
  exact context_env (context_append (context_env h []) [{type:="N",cells:=[some (.natObject slot)]}])
    [("x",⟨s.heap.length,0,[]⟩)]

 theorem keep_frame_free (s : State) (slot : Nat) : LocalsFree (keepFrame s slot) := by
  simp [LocalsFree,keepFrame,allocate,List.lookup]

 theorem keep_frame_x {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (slot : Nat) :
    XContext l (keepFrame s slot) s.heap.length slot := by
  have hp := (List.getElem?_eq_some_iff.mp h.pool_read).choose
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  have hh := (List.getElem?_eq_some_iff.mp h.high_read).choose
  constructor
  · simp [keepFrame,allocate,List.lookup]
  · simp [keepFrame,allocate]
  · omega
  · omega
  · omega

 theorem keep_bind {s : State} {slot value : Nat} (borrow : NatArena.Borrow s.nats slot value) :
    bindArgs Header.layout Generated.f_keep.parameters [.natObject slot] s = some (keepFrame s slot) := by
  have cast := PrimitiveCalls.cast_N (s:={s with env:=[]}) borrow
  simp [Generated.f_keep,bindArgs,List.foldlM,cast,keepFrame]

 /-- The actual keep body writes the old top cell, increments the actual
 global counter, conditionally raises high, and returns the input reference.
 The retained caller state is calculated from these operations, not assumed. -/
 theorem keep_call {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot value : Nat} (h : GenericPoolContext l s cells top high)
    (ht : top < capacity) (borrow : NatArena.Borrow s.nats slot value) :
    SourceCall Header.layout Generated.functions 1 "keep" [.natObject slot] s (.natObject slot)
      (popScope s (keepResult l (keepFrame s slot) cells top high slot)) := by
  have frame := keep_frame_context h slot
  have body := keep_body RuntimeCore.call frame (keep_frame_free s slot) (keep_frame_x h slot) ht borrow
  refine installed_body (cfg:=Header.layout) (rank:=0) (service:=RuntimeCore.call)
    (by simp [Generated.functions]) (fun _ _ _ _ _ r => r) (keep_bind borrow) body ?_
  constructor
  · change castValue Header.layout (keepResult l (keepFrame s slot) cells top high slot) 100 "static N" (.natObject slot) = _
    have live : NatArena.Borrow (keepResult l (keepFrame s slot) cells top high slot).nats slot value := by
      rw [keep_result_nats]
      exact borrow
    have hn : normalizeType "static N" = "N" := by decide +kernel
    change (do let _ ← NatArena.read (keepResult l (keepFrame s slot) cells top high slot).nats slot
               pure (Value.natObject slot)) = some (Value.natObject slot)
    rw [NatArena.read_of_borrow live]
    rfl
  · rfl

end ScopedC.PoolCalls
