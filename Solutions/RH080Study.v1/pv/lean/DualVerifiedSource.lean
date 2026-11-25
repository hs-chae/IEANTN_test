/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualSource
import DualOutput
import DualGridModel

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Verified
open GoldbachDirect

/-- Fixed-input application refinement: the result of the complete actual
parsed C function is the maximum of its separate mathematical grid model.
Both sides are proved, not assumed from an external run. -/
theorem actual_execution_matches_spec :
    Execution.call 1000 "rh_dual_bound" [] = some Model.gridMaximum := by
  rw [Model.gridMaximum_exact]
  exact Execution.actual_numerical_execution

/-- Output-to-mathematics transport. The cap is an unknown result of the actual
source AST execution; this rule cannot be applied by merely giving a desired
decimal bound or a pre-existing grid inequality. -/
theorem source_result_controls_grid {cap : Nat}
    (run : Execution.call 1000 "rh_dual_bound" [] = some cap) :
    ∀ k : Fin 257, Model.sampleBound k.val ≤ cap := by
  have heq : some Model.gridMaximum = some cap := actual_execution_matches_spec.symm.trans run
  have same : Model.gridMaximum = cap := Option.some.inj heq
  intro k
  rw [←same]
  exact Model.sampleBound_le_gridMaximum k

theorem actual_source_grid_cap :
    ∀ k : Fin 257, Model.sampleBound k.val ≤ 1221161 :=
  source_result_controls_grid Execution.actual_numerical_execution

/-- The source/AST, complete numeric execution, application main/serialization
and mathematical cap are all present in the accepted source-first result.
Generic C/compiler/libc/OS/hardware interpretation remains explicitly external.
This is a fixed witness/grid program, not a verified unrestricted optimizer. -/
def SourceFirstOutput : Prop :=
  Correspondence.SourceSyntaxCorresponds RH080PV.source RH080PV.program ∧
  Execution.call 1000 "rh_dual_bound" [] = some 1221161 ∧
  (∀ (PerformedPrintf : Nat → String → Prop) (output : String),
    PerformedPrintf 1221161 output →
      Output.HostMain PerformedPrintf RH080PV.main_ast.body output) ∧
  Output.decimalLine 1221161 = "1221161\n" ∧
  ∀ k : Fin 257, Model.sampleBound k.val ≤ 1221161

theorem actual_source_first_output : SourceFirstOutput :=
  ⟨RH080PV.actual_source_syntax, Execution.actual_numerical_execution,
    (fun _ _ event => Output.actual_host_main event),
    Output.actual_serialized_output, actual_source_grid_cap⟩

#print axioms actual_execution_matches_spec
#print axioms source_result_controls_grid
#print axioms actual_source_grid_cap
#print axioms actual_source_first_output
end RH080PV.Verified
