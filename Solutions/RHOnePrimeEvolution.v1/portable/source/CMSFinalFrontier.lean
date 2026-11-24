/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSWholeFrontier
import CMSSharperUniform

/-! The pointwise effective one-prime frontier consumes both actual branches.
All claims remain explicitly source-conditional on published CMS (6.16). -/
namespace RHOnePrime.CMSFinal
open Real Set
open RHOnePrime.CMSPrime RHOnePrime.CMSOpen

noncomputable def effectiveCoefficient (L : ℝ) : ℝ :=
  min (RHOnePrime.CMSWhole.frontierCoefficient L) (548 / 625)

theorem effective_coefficient_lt_CMS (L : ℝ) :
    effectiveCoefficient L < (22 / 25 : ℝ) := by
  exact (min_le_right _ _).trans_lt (by norm_num)

theorem open_prime_effective_frontier (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeOpen x (x + effectiveCoefficient (log x) * sqrt x * log x) := by
  unfold effectiveCoefficient
  by_cases h : RHOnePrime.CMSWhole.frontierCoefficient (log x) ≤ (548 / 625 : ℝ)
  · rw [min_eq_left h]
    exact RHOnePrime.CMSWhole.open_prime_frontier hCMS rh hx
  · rw [min_eq_right (le_of_not_ge h)]
    exact RHOnePrime.CMSSharper.open_prime_08768 hCMS rh hx

theorem effective_window_strictly_shorter_CMS {x : ℝ} (hx : exp 44 ≤ x) :
    x + effectiveCoefficient (log x) * sqrt x * log x <
      x + (22 / 25) * sqrt x * log x := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hs : 0 < sqrt x := Real.sqrt_pos.mpr hx0
  have ht := mul_lt_mul_of_pos_right (effective_coefficient_lt_CMS (log x)) hs
  have hu := mul_lt_mul_of_pos_right ht (show 0 < log x by linarith)
  linarith

#print axioms open_prime_effective_frontier
#print axioms effective_window_strictly_shorter_CMS
#check @open_prime_effective_frontier
end RHOnePrime.CMSFinal
