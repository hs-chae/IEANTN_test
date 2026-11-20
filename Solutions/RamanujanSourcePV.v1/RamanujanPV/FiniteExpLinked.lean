/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.FiniteExpExecute
namespace RamanujanPV.FiniteExpLinked
open QuotientCMachine
open FiniteExpExecute
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-- Modular calls are accepted only for the separately executed source helper. -/
def service : Service := fun name args =>
  if name="rpc_e_low" then match args with
    | [] => some (.u64 3133965575612453533)
    | _ => none
  else none

theorem low_heap_frame (heap : Heap) : (finalState heap).heap=heap := rfl

theorem service_closed {name : String} {args : List Value} {result : Value}
    (response : service name args=some result) (heap : Heap) :
    name="rpc_e_low" ∧ args=[] ∧
    ∃t, Run noCalls FiniteExpSource.lowFunction.body (initial heap)
      (.returned t result) ∧t.heap=heap := by
  by_cases hname : name="rpc_e_low"
  · subst name
    cases args with
    | nil =>
      have equal : Value.u64 3133965575612453533=result := by simpa [service] using response
      subst result
      exact ⟨rfl,rfl,finalState heap,low_function_executes heap,low_heap_frame heap⟩
    | cons a rest => simp [service] at response
  · simp [service,hname] at response

theorem high_function_executes (heap : Heap) :
    Run service FiniteExpSource.highFunction.body (initial heap)
      (.returned (initial heap) (.u64 3133965575612453555)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence
    (inner:=.returned (initial heap) (.u64 3133965575612453555))
  · exact LCMSourcePV.ASTLoops.SeqRun.returned
      (LCMSourcePV.ASTLoops.StmtRun.returnValue (by rfl))
  · rfl

def LinkedHighRun (heap : Heap) (out : Flow) : Prop :=
  Run service FiniteExpSource.highFunction.body (initial heap) out ∧
  (∀name args result,service name args=some result → ∀h : Heap,
    name="rpc_e_low" ∧args=[] ∧
      ∃t,Run noCalls FiniteExpSource.lowFunction.body (initial h)
        (.returned t result) ∧t.heap=h)

theorem linked_high_executes (heap : Heap) :
    LinkedHighRun heap (.returned (initial heap) (.u64 3133965575612453555)) :=
  ⟨high_function_executes heap,fun _ _ _ response h=>service_closed response h⟩

theorem high_completed_correct {heap : Heap} {t : State} {out : Value}
    (run : LinkedHighRun heap (.returned t out)) :
    out=.u64 (AnalyticTransition.finiteELow+22) := by
  have equal := (QuotientCDeterminism.returned_unique run.1 (high_function_executes heap)).2
  simpa only [AnalyticTransition.finiteELow_value] using equal

/-- The outputs of both actual source functions enclose mathematical e.
The upper function's only call is closed by the actual20-step lower source run. -/
theorem source_outputs_enclose_e {heap : Heap} {s t : State} {low high : Value}
    (hlo : Run noCalls FiniteExpSource.lowFunction.body (initial heap) (.returned s low))
    (hhi : LinkedHighRun heap (.returned t high)) :
    (low.bits:ℝ)/(2:ℝ)^60 ≤ Real.exp 1 ∧
      Real.exp 1 ≤ (high.bits:ℝ)/(2:ℝ)^60 := by
  rw [low_completed_correct hlo,high_completed_correct hhi]
  exact AnalyticTransition.finite_e_enclosure

#print axioms service_closed
#print axioms linked_high_executes
#print axioms high_completed_correct
#print axioms source_outputs_enclose_e
end RamanujanPV.FiniteExpLinked
