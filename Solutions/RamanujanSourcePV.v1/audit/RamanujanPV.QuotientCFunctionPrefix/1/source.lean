/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCInit
import RamanujanPV.QuotientSqrtExecute
import RamanujanPV.QuotientCExecute

/-! Exact count-function prefix. No table values are assumed before execution.
The only modular helper is the source-refined integer square-root service. -/
namespace RamanujanPV.QuotientCFunctionPrefix
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientTables
set_option autoImplicit false
set_option maxHeartbeats 2000000

def input (N capacity sb lb : Nat) (heap : Heap) : State :=
  ⟨bind (bind (bind (bind emptyEnv "n" (.u64 N)) "capacity" (.u64 capacity))
    "small" (.ptr sb)) "large" (.ptr lb),heap⟩

def lowerGuard : Stmt := .branch (.binary "<" (.var "n") (.nat 2))
  (.returnStmt (.nat 0)) .skip
def upperGuard : Stmt := .branch (.binary ">" (.var "n") (.nat 2000000000000))
  (.returnStmt (.nat 0)) .skip
def rootDeclaration : Stmt := .declare [⟨"uint64_t","r",some
  (.call (.var "rpc_isqrt") [.var "n"])⟩]
def capacityGuard : Stmt := .branch (.binary "<=" (.var "capacity") (.var "r"))
  (.returnStmt (.nat 0)) .skip

def prefix : List Stmt :=
  [lowerGuard,upperGuard,rootDeclaration,capacityGuard,QuotientCInit.initFor]

theorem actual_prefix : (match QuotientCSourceV2.countFunction.body with
    | .sequence xs => xs.take 5 | _ => [])=prefix := rfl

/-- Each successful helper response is justified by the actual source helper
body. This fact discloses the modular call contract used by the count execution. -/
theorem helper_source_closed {name : String} {args : List Value} {result : Value}
    (response : QuotientSqrtExecute.service name args=some result) (heap : Heap) :
    ∃ N, name="rpc_isqrt" ∧ args=[.u64 N] ∧ N ≤ 2000000000000 ∧
      ∃ t, Run QuotientSqrtExecute.noCalls QuotientCSourceV2.sqrtFunction.body
        (QuotientSqrtExecute.input N heap) (.returned t result) ∧ t.heap=heap := by
  exact QuotientSqrtExecute.service_closed response heap

/-- Actual source prefix, from arbitrary allocated buffer contents to the
proved initialized quotient tables; all source failure guards are discharged. -/
theorem prefix_exec {s : State} {sb lb N capacity : Nat}
    (hN2 : 2 ≤ N) (hN : N ≤ 2000000000000) (hcap : N.sqrt < capacity)
    (owned : Owned s.heap) (buffers : QuotientCInit.Buffers s.heap sb lb N.sqrt)
    (hn : s.env "n"=some (.u64 N))
    (hc : s.env "capacity"=some (.u64 capacity))
    (hs : s.env "small"=some (.ptr sb)) (hl : s.env "large"=some (.ptr lb))
    (freshR : s.env "r"=none) (freshI : s.env "i"=none) :
    ∃ t, SeqRun QuotientSqrtExecute.service prefix s (.continuing t) ∧
      t.env=bind s.env "r" (.u64 N.sqrt) ∧ Owned t.heap ∧
      QuotientCExecute.HeapRep t.heap sb lb N.sqrt (initial N) := by
  have hNw : N < modulus := by norm_num [modulus]; omega
  have hrw : N.sqrt < modulus := (Nat.sqrt_le_self N).trans_lt hNw
  have lowerEval : Eval QuotientSqrtExecute.service (.binary "<" (.var "n") (.nat 2))
      s s (.i32 0) :=
    eval_pure_lt (pure_binary_of
      ((pure_var QuotientSqrtExecute.service s.heap s.env 6 "n").trans hn)
      ((pure_literal QuotientSqrtExecute.service s.heap s.env 6 2).trans (by norm_num [literal]))
      (by simp [binary,Value.scalar,show ¬N<2 by omega]))
  have upperEval : Eval QuotientSqrtExecute.service (.binary ">" (.var "n") (.nat 2000000000000))
      s s (.i32 0) :=
    eval_pure_gt (pure_binary_of
      ((pure_var QuotientSqrtExecute.service s.heap s.env 6 "n").trans hn)
      ((pure_literal QuotientSqrtExecute.service s.heap s.env 6 2000000000000).trans literal_two_trillion)
      (by simp [binary,Value.scalar,show ¬2000000000000<N by omega]))
  have lowerRun : Run QuotientSqrtExecute.service lowerGuard s (.continuing s) := by
    apply StmtRun.branch lowerEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval QuotientSqrtExecute.service)
      (Declare:=Declare QuotientSqrtExecute.service) (truth:=truth) (Scope:=Scope) s
  have upperRun : Run QuotientSqrtExecute.service upperGuard s (.continuing s) := by
    apply StmtRun.branch upperEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval QuotientSqrtExecute.service)
      (Declare:=Declare QuotientSqrtExecute.service) (truth:=truth) (Scope:=Scope) s
  let started : State := {s with env:=bind s.env "r" (.u64 N.sqrt)}
  have rootEval : Declare QuotientSqrtExecute.service [⟨"uint64_t","r",some
      (.call (.var "rpc_isqrt") [.var "n"])⟩] s started :=
    declare_singleton_of freshR
      (pure_call_one_of ((pure_var QuotientSqrtExecute.service s.heap s.env 6 "n").trans hn)
        (by simp [QuotientSqrtExecute.service,hN])) (uint64_of_u64 hrw)
  have hroot : started.env "r"=some (.u64 N.sqrt) := by simp [started]
  have hcapacity : started.env "capacity"=some (.u64 capacity) := by simp [started,hc]
  have capacityEval : Eval QuotientSqrtExecute.service (.binary "<=" (.var "capacity") (.var "r"))
      started started (.i32 0) :=
    (eval_le_of ((pure_var QuotientSqrtExecute.service started.heap started.env 6 "capacity").trans hcapacity)
      ((pure_var QuotientSqrtExecute.service started.heap started.env 6 "r").trans hroot)).trans
      (by rw [if_neg (by omega : ¬capacity ≤ N.sqrt)])
  have capacityRun : Run QuotientSqrtExecute.service capacityGuard started (.continuing started) := by
    apply StmtRun.branch capacityEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval QuotientSqrtExecute.service)
      (Declare:=Declare QuotientSqrtExecute.service) (truth:=truth) (Scope:=Scope) started
  obtain ⟨t,initRun,envt,ownedt,rept⟩ := QuotientCInit.initialization_loop (s:=started)
    owned buffers (by simp [started,hs]) (by simp [started,hl])
    (by simp [started,hn]) hroot (by simp [started,freshI]) (Nat.sqrt_le_self N) hN
  refine ⟨t,?_,envt,ownedt,rept⟩
  exact SeqRun.next lowerRun (SeqRun.next upperRun
    (SeqRun.next (StmtRun.declare rootEval) (SeqRun.next capacityRun
      (SeqRun.next initRun (SeqRun.nil t)))))

#print axioms actual_prefix
#print axioms helper_source_closed
#print axioms prefix_exec
end RamanujanPV.QuotientCFunctionPrefix
