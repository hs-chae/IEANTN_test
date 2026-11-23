/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PsiBoxExact
import PsiElementary

namespace RHContinuation.Parabolic
open Real PsiSmoothing

/-- Strongest actual-psi consumer after proving both elementary averaging inputs.
Only the exact analytic explicit-formula/zero-density/Mellin contracts remain. -/
theorem psi_fast (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula box) (hz : ZeroDensityMomentEstimate box)
    (h0 : J box 0 = Real.log 2) (h1 : J box 1 ≤ 567 / 800) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (Real.log 2) (567 / 800) (Real.log x) :=
  PsiBoxExact.psi_fast rh hef hz PsiElementary.box_main PsiElementary.box_trivial h0 h1

/-- Required originalB5 provider on the whole actual real-x ray, with all newly
proved elementary support/normalization/main/trivial obligations discharged. -/
theorem psi_B5 (rh : RiemannHypothesis)
    (hef : AveragedExplicitFormula parabola) (hz : ZeroDensityMomentEstimate parabola)
    (h0 : J parabola 0 ≤ 831 / 1000) (h1 : J parabola 1 ≤ 287 / 500) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x - x| ≤
      Real.sqrt x * envelope (831 / 1000) (287 / 500) (Real.log x) := by
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos 35).trans_le hx
  have hlog : 35 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 35) hx
    simpa only [Real.log_exp] using h
  have h := PsiSmoothing.psi_B5 rh hef hz PsiElementary.parabola_main
    PsiElementary.parabola_trivial h0 h1 (Real.log x) hlog
  simpa only [Real.exp_log hx0] using h

#print axioms psi_fast
#print axioms psi_B5
end RHContinuation.Parabolic
