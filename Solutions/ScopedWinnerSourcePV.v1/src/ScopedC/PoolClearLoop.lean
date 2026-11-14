/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolClearMemory

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 def clearCondition : Expr := .binary ">" (.var "poolTop") (.var "mark")
 def clearBody : Stmt := .sequence [
  .eval (.binary "=" (.var "poolTop") (.binary "-" (.var "poolTop") (.nat 1))),
  .eval (.call (.var "lean_dec") [.index (.var "pool") (.var "poolTop")])]
 def clearResult (l : PoolLayout) (s : State) (mark : Nat) (released : List Nat) : State :=
  {storeTop l s mark with nats:=NatArena.clear s.nats released}

 theorem clear_iteration {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot : Nat} {arena : NatArena.Arena}
    (h : GenericPoolContext l s cells top high) (free : LocalsFree s)
    (hp : 0 < top) (hc : top ≤ capacity)
    (cell : cells[top-1]? = some (some (.natObject slot)))
    (release : NatArena.release s.nats slot = some arena) :
    Run Header.layout RuntimeCore.call clearBody s
      (.continuing {storeTop l s (top-1) with nats:=arena}) := by
  let mid := storeTop l s (top-1)
  let final := {mid with nats:=arena}
  have hm : GenericPoolContext l mid cells (top-1) high :=
    context_store_top h (by have := h.top_range;omega)
  have fm : LocalsFree mid := free
  have decr := eval_decrement RuntimeCore.call h free hp
  have dec : Eval Header.layout RuntimeCore.call
      (.call (.var "lean_dec") [.index (.var "pool") (.var "poolTop")]) mid final .unit := by
    refine ⟨6,?_⟩
    exact eval_call_one RuntimeCore.call (eval_pool_index RuntimeCore.call hm fm (by omega) cell)
      (runtime_release release)
  apply Loops.StmtRun.sequence
    (Loops.SeqRun.next (Loops.StmtRun.evaluate decr)
      (Loops.SeqRun.next (Loops.StmtRun.evaluate dec) (Loops.SeqRun.nil final)))
  change final = popScope s final
  exact (pop_same (s:=s) (t:=final) (by simp [final,mid,storeTop,storeObject]) rfl).symm

 theorem clear_loop_done {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high i : Nat} (h : GenericPoolContext l s cells top high) (free : LocalsFree s)
    (mark : MarkContext l s i top) :
    Loops.WhileRun (Eval Header.layout RuntimeCore.call) (Declare Header.layout RuntimeCore.call)
      truth Scope clearCondition clearBody s (.continuing s) := by
  exact Loops.WhileRun.done (eval_clear_guard RuntimeCore.call h free mark le_rfl)
    (by rw [truth_boolean];simp)

 /-- The source's descending while loop releases exactly the owned tokens
 above mark. Each step consumes an actual array read and runtime release. -/
 theorem clear_loop {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {refs : List Nat} {high mark i : Nat}
    (h : GenericPoolContext l s cells refs.length high) (free : LocalsFree s)
    (param : MarkContext l s i mark) (hmark : mark ≤ refs.length)
    (hc : refs.length ≤ capacity) (entries : PoolEntries cells refs)
    (valid : RefsValid s.nats refs) (owned : NatArena.PoolOwned s.nats refs) :
    Loops.WhileRun (Eval Header.layout RuntimeCore.call) (Declare Header.layout RuntimeCore.call)
      truth Scope clearCondition clearBody s
      (.continuing (clearResult l s mark (refs.take (refs.length-mark)))) := by
  induction refs generalizing s with
  | nil =>
    have hz : mark = 0 := by simpa using hmark
    subst mark
    have done := clear_loop_done h free param
    have hs : storeTop l s 0 = s := store_top_same h
    simpa only [clearResult,List.length_nil,Nat.sub_self,List.take_zero,clear_nil,hs] using done
  | cons first rest ih =>
    by_cases done : mark = (first::rest).length
    · subst mark
      have hd := clear_loop_done h free param
      simpa only [clearResult,Nat.sub_self,List.take_zero,clear_nil,store_top_same h] using hd
    · have hm : mark ≤ rest.length := by simp only [List.length_cons] at hmark done;omega
      obtain ⟨arena,release,ownRest,validRest,clearRest,values⟩ := release_owned_cons valid owned
      let mid : State := {storeTop l s rest.length with nats:=arena}
      have hr : rest.length < 2^32 := by have := h.top_range;simp only [List.length_cons] at this;omega
      have hmid : GenericPoolContext l mid cells rest.length high := context_nats (context_store_top h hr) arena
      have fmid : LocalsFree mid := free
      have pmid : MarkContext l mid i mark := mark_nats (mark_store_top param) arena
      have step : Run Header.layout RuntimeCore.call clearBody s (.continuing mid) := by
        simpa only [List.length_cons,Nat.add_sub_cancel,mid] using
          clear_iteration h free (by simp) hc (by simpa using entries_head entries) release
      have restRun := ih hmid fmid pmid hm (by simp only [List.length_cons] at hc;omega)
        (entries_tail entries) validRest ownRest
      have take_eq : (first::rest).take ((first::rest).length-mark) =
          first::rest.take (rest.length-mark) := by
        have ha : (first::rest).length-mark = (rest.length-mark)+1 := by simp only [List.length_cons];omega
        rw [ha]
        rfl
      have finish_eq : clearResult l mid mark (rest.take (rest.length-mark)) =
          clearResult l s mark ((first::rest).take ((first::rest).length-mark)) := by
        simp only [clearResult,mid,storeTop,storeObject,List.set_set,take_eq]
        rw [release_clear_eq release]
      rw [finish_eq] at restRun
      apply Loops.WhileRun.next (eval_clear_guard RuntimeCore.call h free param hmark) ?_ step restRun
      rw [truth_boolean]
      simp only [decide_eq_true_eq]
      simp only [List.length_cons] at hmark done ⊢
      omega

end ScopedC.PoolCalls
