/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolClearLoop

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 theorem clear_result_shape (l : PoolLayout) (s : State) (mark : Nat) (released : List Nat) :
    (clearResult l s mark released).heap.length = s.heap.length ∧
    (clearResult l s mark released).env = s.env ∧
    (clearResult l s mark released).globals = s.globals := by
  simp [clearResult,storeTop,storeObject]

 theorem clear_body {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {refs : List Nat} {high mark i : Nat}
    (h : GenericPoolContext l s cells refs.length high) (free : LocalsFree s)
    (param : MarkContext l s i mark) (hmark : mark ≤ refs.length)
    (hc : refs.length ≤ capacity) (entries : PoolEntries cells refs)
    (valid : RefsValid s.nats refs) (owned : NatArena.PoolOwned s.nats refs) :
    Run Header.layout RuntimeCore.call Generated.f_clearTo.body s
      (.continuing (clearResult l s mark (refs.take (refs.length-mark)))) := by
  let final := clearResult l s mark (refs.take (refs.length-mark))
  have first : Run Header.layout RuntimeCore.call
      (.branch (.binary ">" (.var "mark") (.var "poolTop")) (.eval (.call (.var "fail") [])) .skip)
      s (.continuing s) := by
    apply Loops.StmtRun.branch (eval_bad_mark_guard RuntimeCore.call h free param hmark)
    exact Loops.StmtRun.skip s
  have loop : Run Header.layout RuntimeCore.call (.whileLoop clearCondition clearBody) s (.continuing final) :=
    Loops.StmtRun.whileLoop (clear_loop h free param hmark hc entries valid owned)
  apply Loops.StmtRun.sequence (Loops.SeqRun.next first
    (Loops.SeqRun.next loop (Loops.SeqRun.nil final)))
  change final = popScope s final
  exact (pop_same (s:=s) (t:=final) (clear_result_shape l s mark _).1
    (clear_result_shape l s mark _).2.1).symm

 def clearFrame (s : State) (mark : Nat) : State :=
  allocate {s with env:=[]} "unsigned int" "mark" (some (word mark))

 theorem clear_frame_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (mark : Nat) :
    GenericPoolContext l (clearFrame s mark) cells top high := by
  exact context_env (context_append (context_env h []) [{type:="unsigned int",cells:=[some (word mark)]}])
    [("mark",⟨s.heap.length,0,[]⟩)]

 theorem clear_frame_free (s : State) (mark : Nat) : LocalsFree (clearFrame s mark) := by
  simp [LocalsFree,clearFrame,allocate,List.lookup]

 theorem clear_frame_mark {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (mark : Nat) :
    MarkContext l (clearFrame s mark) s.heap.length mark := by
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  constructor
  · simp [clearFrame,allocate,List.lookup]
  · simp [clearFrame,allocate]
  · omega

 theorem cast_unsigned_int (s : State) (mark : Nat) (range : mark < 2^32) :
    castValue Header.layout s 100 "unsigned int" (word mark) = some (word mark) := by
  change (Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(mark:Int)⟩ >>= fun x => some (Value.integer x)) = _
  rw [scalar_u32_cast mark range]
  rfl

 theorem clear_bind (s : State) (mark : Nat) (range : mark < 2^32) :
    bindArgs Header.layout Generated.f_clearTo.parameters [word mark] s = some (clearFrame s mark) := by
  have cast := cast_unsigned_int {s with env:=[]} mark range
  simp [Generated.f_clearTo,bindArgs,List.foldlM,cast,clearFrame]

 theorem clear_result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (mark : Nat) (released : List Nat) :
    clearResult l (clearFrame s mark) mark released = clearFrame (clearResult l s mark released) mark := by
  have ht := (List.getElem?_eq_some_iff.mp h.top_read).choose
  simp [clearResult,clearFrame,allocate,storeTop,storeObject,List.set_append_left l.top _ ht]

 theorem pop_clear_frame {s t : State} (mark : Nat)
    (hlen : t.heap.length = s.heap.length) (henv : t.env = s.env) :
    popScope s (clearFrame t mark) = t := by
  cases t
  simp_all [popScope,clearFrame,allocate]

 /-- Complete fixed source-function execution, with no application callback
 oracle. The pool releases exactly the descending prefix of active refs. -/
 theorem clear_call_canonical {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {refs : List Nat} {high mark : Nat}
    (h : GenericPoolContext l s cells refs.length high) (hmark : mark ≤ refs.length)
    (hc : refs.length ≤ capacity) (entries : PoolEntries cells refs)
    (valid : RefsValid s.nats refs) (owned : NatArena.PoolOwned s.nats refs) :
    SourceCall Header.layout Generated.functions 1 "clearTo" [word mark] s .unit
      (clearResult l s mark (refs.take (refs.length-mark))) := by
  have range : mark < 2^32 := by have := h.top_range;omega
  have body := clear_body (clear_frame_context h mark) (clear_frame_free s mark)
    (clear_frame_mark h mark) hmark hc entries valid owned
  have old : SourceCall Header.layout Generated.functions 1 "clearTo" [word mark] s .unit
      (popScope s (clearResult l (clearFrame s mark) mark (refs.take (refs.length-mark)))) := by
    refine installed_body (cfg:=Header.layout) (rank:=0) (service:=RuntimeCore.call)
      (by simp [Generated.functions]) (fun _ _ _ _ _ r => r) (clear_bind s mark range) body ?_
    exact ⟨by decide +kernel,rfl,rfl⟩
  rw [clear_result_frame h,pop_clear_frame mark (clear_result_shape l s mark _).1
    (clear_result_shape l s mark _).2.1] at old
  exact old

end ScopedC.PoolCalls
