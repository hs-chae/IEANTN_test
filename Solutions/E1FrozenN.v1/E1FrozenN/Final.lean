/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.PrimeRay
import E1FrozenN.Interval.Assembly
import PVEvolutionA.Pointwise
namespace E1FrozenN
noncomputable def finalErrorBound (x:ℝ) : ℝ :=
  min (errorBound x) ((9150520021/1000000000000+1/10^28:ℝ)*x^(-(1:ℝ)/8))
theorem final_pair (hs : DirectCH2Inputs)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp (330:ℝ)≤x) :
    IEANTN.Eψ x≤finalErrorBound x ∧
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤finalErrorBound x := by
  have hp := baseline_pair hs h hRH hqrh hx
  have hpsi := psi_tight330 hs h hRH hqrh hx
  have hweighted := lambda_tight330 hs h hRH hqrh hx
  have heq : (9150520022/1000000000000-1/10^12+1/10^28:ℝ)=
      9150520021/1000000000000+1/10^28 := by norm_num
  rw [heq] at hpsi hweighted
  exact ⟨le_min hp.1 hpsi,le_min hp.2 hweighted⟩
#print axioms final_pair
end E1FrozenN
