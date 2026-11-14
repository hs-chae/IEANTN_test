/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolInvariants

namespace ScopedC.HelperCodeAdapters
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PrimitiveCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem comparison_call_for_code (code : List Function) (f : Function) (runtime : String) (result : Bool)
    (installed : f ∈ code)
    (parameters : f.parameters = [("N","a"),("N","b")])
    (returns : f.returnType = "static unsigned int")
    (body : f.body = .sequence [.returnStmt (.cast "unsigned int"
      (.call (.var runtime) [.var "a",.var "b"]))])
    {s : State} {a b n m : Nat}
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m)
    (answer : RuntimeCore.call runtime [.natObject a,.natObject b] (frame s a b) =
      some (u8 result,frame s a b)) :
    SourceCall Header.layout code 1 f.name
      [.natObject a,.natObject b] s (u32 result) s := by
  have expression : Eval Header.layout RuntimeCore.call
      (.cast "unsigned int" (.call (.var runtime) [.var "a",.var "b"]))
      (frame s a b) (frame s a b) (u32 result) := by
    refine ⟨8,?_⟩
    rw [evalExpr]
    have hc : evalExpr Header.layout RuntimeCore.call 7 (frame s a b)
        (.call (.var runtime) [.var "a",.var "b"]) = some (u8 result,frame s a b) := by
      rw [evalExpr]
      simp only [List.foldlM,eval_var_a,eval_var_b,Option.bind_some,
        List.nil_append,List.append_nil,answer]
      simp only [bind,Option.bind,pure,eval_var_b,List.cons_append,List.nil_append,answer]
    rw [hc]
    simp [cast8]
  have statement : Run Header.layout RuntimeCore.call f.body (frame s a b)
      (.returned (frame s a b) (u32 result)) := by
    rw [body]
    exact Loops.StmtRun.sequence
      (Loops.SeqRun.returned (Loops.StmtRun.returnValue expression)) ⟨rfl,(pop_self _).symm⟩
  refine installed_body (cfg:=Header.layout) (code:=code) (rank:=0) (service:=RuntimeCore.call)
    installed (fun _ _ _ _ _ h => h) ?_ statement ?_
  · simpa only [parameters] using frame_bind ha hb
  · change castValue Header.layout (frame s a b) 100 f.returnType (u32 result) =
        some (u32 result) ∧ s = popScope s (frame s a b)
    exact ⟨by simpa only [returns] using cast32 (frame s a b) result,(pop_frame s a b).symm⟩

 theorem ne_for_code (code : List Function) (installed : Generated.f_ne ∈ code)
    {s : State} {a b n m : Nat} (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 1 "ne" [.natObject a,.natObject b] s (u32 (n==m)) s := by
  exact comparison_call_for_code code Generated.f_ne "lean_nat_dec_eq" (n==m)
    installed rfl rfl rfl ha hb (eq_runtime (s:=frame s a b) ha hb)
 theorem nle_for_code (code : List Function) (installed : Generated.f_nle ∈ code)
    {s : State} {a b n m : Nat} (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 1 "nle" [.natObject a,.natObject b] s (u32 (decide (n ≤ m))) s := by
  exact comparison_call_for_code code Generated.f_nle "lean_nat_dec_le" (decide (n ≤ m))
    installed rfl rfl rfl ha hb (le_runtime (s:=frame s a b) ha hb)
 theorem nlt_for_code (code : List Function) (installed : Generated.f_nlt ∈ code)
    {s : State} {a b n m : Nat} (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 1 "nlt" [.natObject a,.natObject b] s (u32 (decide (n < m))) s := by
  exact comparison_call_for_code code Generated.f_nlt "lean_nat_dec_lt" (decide (n < m))
    installed rfl rfl rfl ha hb (lt_runtime (s:=frame s a b) ha hb)

 theorem keep_for_code (code : List Function) (installed : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high slot value : Nat}
    (h : GenericPoolContext l s cells top high) (ht : top < capacity)
    (borrow : NatArena.Borrow s.nats slot value) :
    SourceCall Header.layout code 1 "keep" [.natObject slot] s (.natObject slot)
      (keepResult l s cells top high slot) := by
  have ctx := keep_frame_context h slot
  have body := keep_body RuntimeCore.call ctx (keep_frame_free s slot) (keep_frame_x h slot) ht borrow
  have old : SourceCall Header.layout code 1 "keep" [.natObject slot] s (.natObject slot)
      (popScope s (keepResult l (keepFrame s slot) cells top high slot)) := by
    refine installed_body (cfg:=Header.layout) (code:=code) (rank:=0) (service:=RuntimeCore.call)
      installed (fun _ _ _ _ _ r => r) (keep_bind borrow) body ?_
    constructor
    · change (do let _ ← NatArena.read (keepResult l (keepFrame s slot) cells top high slot).nats slot
                 pure (Value.natObject slot)) = some (Value.natObject slot)
      have live : NatArena.Borrow (keepResult l (keepFrame s slot) cells top high slot).nats slot value := by
        rw [keep_result_nats]
        exact borrow
      rw [NatArena.read_of_borrow live]
      rfl
    · rfl
  rw [keep_result_frame h,pop_keep_frame slot (keep_result_shape l s cells top high slot).1
    (keep_result_shape l s cells top high slot).2.1] at old
  exact old

 theorem clear_for_code (code : List Function) (installed : Generated.f_clearTo ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)} {refs : List Nat} {high mark : Nat}
    (h : GenericPoolContext l s cells refs.length high) (hmark : mark ≤ refs.length)
    (hc : refs.length ≤ capacity) (entries : PoolEntries cells refs)
    (valid : RefsValid s.nats refs) (owned : NatArena.PoolOwned s.nats refs) :
    SourceCall Header.layout code 1 "clearTo" [word mark] s .unit
      (clearResult l s mark (refs.take (refs.length-mark))) := by
  have range : mark < 2^32 := by have := h.top_range;omega
  have body := clear_body (clear_frame_context h mark) (clear_frame_free s mark)
    (clear_frame_mark h mark) hmark hc entries valid owned
  have old : SourceCall Header.layout code 1 "clearTo" [word mark] s .unit
      (popScope s (clearResult l (clearFrame s mark) mark (refs.take (refs.length-mark)))) := by
    refine installed_body (cfg:=Header.layout) (code:=code) (rank:=0) (service:=RuntimeCore.call)
      installed (fun _ _ _ _ _ r => r) (clear_bind s mark range) body ?_
    exact ⟨by decide +kernel,rfl,rfl⟩
  rw [clear_result_frame h,pop_clear_frame mark (clear_result_shape l s mark _).1
    (clear_result_shape l s mark _).2.1] at old
  exact old

end ScopedC.HelperCodeAdapters
