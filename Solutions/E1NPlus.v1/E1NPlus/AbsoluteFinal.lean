/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Absolute
namespace E1NPlus
open Real Set E1FrozenN
set_option maxHeartbeats 0
noncomputable def pairBound (x:ℝ):ℝ:=
  min (gridInfBound x) (if exp (330:ℝ) ≤ x then E1FrozenN.finalErrorBound x
    else (9468285637/1000000000000:ℝ)*x^(-(1:ℝ)/8))
noncomputable def piGridBound (n:ℕ+) (x:ℝ):ℝ:=
  ((1+33/10000000000000000)*PVEvolutionA.Sloped.coefficient (n:ℕ) (log x) (log x/3)+
    1/10^28+1/10^13)*x^(-(1:ℝ)/8)
noncomputable def piInfBound (x:ℝ):ℝ:=⨅n:ℕ+,piGridBound n x
noncomputable def piBound (x:ℝ):ℝ:=min (PVEvolutionA.bestBound x) (piInfBound x)

theorem pair_full (hs:DirectCH2Inputs)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    IEANTN.Eψ x ≤ pairBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ pairBound x := by
  have hp:=pair_grid_inf hs h hRH hQRH hx
  by_cases h330:exp (330:ℝ) ≤ x
  · have hn:=E1FrozenN.final_pair hs h hRH hQRH h330
    exact ⟨le_min hp.1 (by simpa [pairBound,h330] using hn.1),
      le_min hp.2 (by simpa [pairBound,h330] using hn.2)⟩
  · have hn:=pair300 hs h hRH hQRH hx
    exact ⟨le_min hp.1 (by simpa [h330] using hn.1),
      le_min hp.2 (by simpa [h330] using hn.2)⟩

theorem pi_grid (hCHJ:WinnerDirectKernel.OriginalCHJSource)
    (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (n:ℕ+) {x:ℝ} (hx:exp (300:ℝ) ≤ x):IEANTN.Eπ x ≤ piGridBound n x := by
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:300 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hh:=PVEvolutionA.PointwiseConsumer.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    n.pos hL (le_rfl:PVEvolutionA.Sloped.coefficient (n:ℕ) (log x) (log x/3) ≤
      PVEvolutionA.Sloped.coefficient (n:ℕ) (log x) (log x/3)) x (by rw [exp_log hx0])
  simp only [pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] at hh
  convert hh using 1 <;> norm_num [piGridBound]

theorem pi_full (hCHJ:WinnerDirectKernel.OriginalCHJSource)
    (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:exp (300:ℝ) ≤ x):IEANTN.Eπ x ≤ piBound x := by
  refine le_min (PVEvolutionA.pi_best hCHJ hrvm hsmall hlow h hRH hQRH hx) ?_
  apply le_ciInf
  intro n
  exact pi_grid hCHJ hrvm hsmall hlow h hRH hQRH n hx

#print axioms pair_full
#print axioms pi_full
end E1NPlus
