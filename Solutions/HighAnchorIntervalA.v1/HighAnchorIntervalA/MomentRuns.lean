/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.MomentProgram
namespace HighAnchorIntervalA.Numerical
open WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem moment_domains : ∀i:Fin cells,(momentOutput i).2=true := by native_decide
theorem budget_checked : acceptUpper [budgetOutput] [target]=true := by native_decide

theorem rejects_zero_first_cap : acceptUpper [momentOutput ⟨0,by decide⟩] [(0:ℚ)]=false := by native_decide
theorem rejects_too_small_cap : acceptUpper [budgetOutput] [(918/1000:ℚ)]=false := by native_decide

#print axioms moment_domains
#print axioms budget_checked
end HighAnchorIntervalA.Numerical
