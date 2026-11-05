/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightCertificate
namespace WinnerDensityA.HeightSharpCertificate
open WinnerProgramA
/-- Retain the exact accepted sum instead of rounding its already executed
upper enclosure to six decimal places. No new native fact is introduced. -/
theorem coefficient300 : HeightProgram.rowCoefficient 8192 300 100≤9474448/1000000000 := by
  have h:=source_linked_upper (HeightProgram.program 300 100 8192)
    (run (HeightProgram.program 300 100 8192)) HeightCertificate.bounds rfl HeightCertificate.checked
  rw [HeightProgram.program_semantics _ _ (by decide : 0<(8192:ℕ)) (by norm_num)] at h
  norm_num [HeightCertificate.bounds] at h ⊢
  exact h
#print axioms coefficient300
end WinnerDensityA.HeightSharpCertificate
