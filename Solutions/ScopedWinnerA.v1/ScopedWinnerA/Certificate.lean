/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightProgram
import Lean
namespace ScopedWinnerA.Certificate
open WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Upward enclosures proposed before execution; acceptance checks every cell and domain. -/
def bounds : List ℚ := [2/1000000000,9471450/1000000000]
def program := WinnerDensityA.HeightProgram.program 300 100 16384
/-- Fresh execution of 16385 actual cells, not an assumed mathematical budget. -/
theorem checked : acceptUpper (run program) bounds = true := by native_decide
/-- The generic interval soundness and syntax denotation consume the executed enclosure. -/
theorem coefficient300 : WinnerDensityA.HeightProgram.rowCoefficient 16384 300 100 ≤
    (9471452/1000000000 : ℝ) := by
  have h := source_linked_upper program (run program) bounds rfl checked
  rw [show program = WinnerDensityA.HeightProgram.program 300 100 16384 from rfl,
    WinnerDensityA.HeightProgram.program_semantics _ _ (by decide : 0<(16384:ℕ)) (by norm_num)] at h
  norm_num [bounds] at h ⊢
  exact h
#print axioms coefficient300
end ScopedWinnerA.Certificate
