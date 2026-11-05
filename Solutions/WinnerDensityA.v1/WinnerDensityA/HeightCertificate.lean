/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightProgram
import Lean
namespace WinnerDensityA.HeightCertificate
open WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def bounds : List ℚ := [2/1000000000,9474446/1000000000]
theorem checked : acceptUpper (run (HeightProgram.program 300 100 8192)) bounds=true := by native_decide
/-- Exact executed four-height coefficient, including all low-zero terms. -/
theorem coefficient300 : HeightProgram.rowCoefficient 8192 300 100≤9475/1000000 := by
  have h:=source_linked_upper (HeightProgram.program 300 100 8192)
    (run (HeightProgram.program 300 100 8192)) bounds rfl checked
  rw [HeightProgram.program_semantics _ _ (by decide : 0<(8192:ℕ)) (by norm_num)] at h
  norm_num [bounds] at h ⊢
  linarith
#print axioms coefficient300
end WinnerDensityA.HeightCertificate
