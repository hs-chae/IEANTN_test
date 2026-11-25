/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualOutput
import DualModel

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.BoundaryControls

theorem changed_numerical_output_rejected :
    Execution.call 1000 "jump_positive" [4] ≠ some 838 := by decide +kernel

theorem missing_newline_rejected : Output.decimalLine 1221161 ≠ "1221161" := by decide +kernel

theorem missing_fold_endpoint_rejected : ¬ (Model.reducedAngle 1 128).1 ≤ 127 := by decide +kernel

/-- A failed printf can capture no bytes while main still returns zero. This
relation is permitted explicitly; it is not promoted to a successful I/O fact. -/
def EmptyCapture (_ : Nat) (output : String) : Prop := output=""

theorem actual_main_allows_empty_capture :
    Output.HostMain EmptyCapture RH080PV.main_ast.body "" :=
  Output.actual_host_main rfl

theorem empty_capture_is_not_successful : ¬Output.SuccessfulPrintfContract EmptyCapture := by
  intro success
  have bad := success 1221161 "" rfl
  have different : ("" : String) ≠ Output.decimalLine 1221161 := by decide +kernel
  exact different bad

#print axioms changed_numerical_output_rejected
#print axioms actual_main_allows_empty_capture
#print axioms empty_capture_is_not_successful
end RH080PV.BoundaryControls
