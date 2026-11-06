/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.EvolvedSemantics

namespace DirectIntervalA.Evolved
open WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem moment_domains : ∀i:Fin cells,(momentOutput i).2=true := by native_decide

theorem budget_checked : acceptUpper [budgetOutput] [target]=true := by native_decide

/-- A lower enclosure of the actual 512-cell budget permits a strict comparison
of executed allowance expressions, rather than just rounded upper caps. -/
theorem baseline_lower_checked :
    acceptLower [Numerical.budgetOutput] [(358513/1000000:ℚ)]=true := by native_decide

theorem rejects_zero_first_cap :
    acceptUpper [momentOutput ⟨0,by decide⟩] [(0:ℚ)]=false := by native_decide

theorem rejects_too_small_cap : acceptUpper [budgetOutput] [(35/100:ℚ)]=false := by native_decide

end DirectIntervalA.Evolved
#print axioms DirectIntervalA.Evolved.budget_checked
