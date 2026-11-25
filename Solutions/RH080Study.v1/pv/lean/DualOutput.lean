/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualHostSemantics
import DualActualRun
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RH080PV.Output
open GoldbachDirect
theorem actual_numerical_word : 1221161 < Execution.wordLimit := by decide

theorem actual_host_main {PerformedPrintf : Nat → String → Prop} {output : String}
    (performed : PerformedPrintf 1221161 output) :
    HostMain PerformedPrintf RH080PV.main_ast.body output := by
  apply HostMain.printReturn
  change PrintAction PerformedPrintf (.call "printf" [.literal (.string "%llu\n"),
    .cast .ull (.call "rh_dual_bound" [])]) output
  have called : HostExpr (.call "rh_dual_bound" []) 1221161 :=
    .call .nil Execution.actual_numerical_execution
  have printed := PrintAction.unsignedLine (HostExpr.castULL called actual_numerical_word) performed
  exact printed

theorem actual_serialized_output : decimalLine 1221161 = "1221161\n" := by decide

theorem actual_successful_capture {PerformedPrintf : Nat → String → Prop} {output : String}
    (performed : PerformedPrintf 1221161 output)
    (contract : SuccessfulPrintfContract PerformedPrintf) :
    HostMain PerformedPrintf RH080PV.main_ast.body output ∧ output="1221161\n" := by
  refine ⟨actual_host_main performed,?_⟩
  exact (contract 1221161 output performed).trans actual_serialized_output

#print axioms actual_host_main
#print axioms actual_serialized_output
#print axioms actual_successful_capture
end RH080PV.Output
