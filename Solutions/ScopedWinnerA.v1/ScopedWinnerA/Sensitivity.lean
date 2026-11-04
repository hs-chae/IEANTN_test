/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Numerical
namespace ScopedWinnerA.Sensitivity
open WinnerProgramA WinnerBetaA.Numerical
set_option maxHeartbeats 0
/-- Four legitimate changed beta inputs to the SAME generic interval coefficient algorithm. -/
def scenarios : List (ℚ × ℚ) := [(7/8,19026839/10000000000),(9/10,13343142/10000000000),(15/16,6682697/10000000000),(31/32,2842002/10000000000)]
def accepted : Bool := scenarios.all fun z => check z.1 240 z.2
/-- Numerical coefficient certificates only; this does not assert new15/16 or31/32 prime transfers. -/
theorem checked : accepted = true := by native_decide
/-- Denotation and generic interval soundness are reused for every accepted changed input. -/
theorem coefficient_bound (β C : ℚ) (hmem : (β,C) ∈ scenarios) :
    WinnerBetaA.pairedCoefficient β 240 ≤ (C:ℝ) := by
  have h := (List.all_eq_true.mp checked) (β,C) hmem
  exact coefficient_upper β 240 C h
#print axioms coefficient_bound
end ScopedWinnerA.Sensitivity
