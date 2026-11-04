/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GeneralStrip
import WinnerBetaA.Theta

namespace WinnerBetaA
open Real IEANTN CH2QRH CH2.v7

/-- The coefficient actually evaluated by the numerical application. -/
noncomputable def pairedCoefficient (β L : ℝ) : ℝ :=
  (500001 / 1000000 : ℝ) *
    ((1 - β)^2 / (2 * Real.pi) + (2 + 1 / Real.pi) * (1 - β) / L) +
      (16 / 5 : ℝ) / L^2

/-- This finite expression decreases as the onset grows. No error-function monotonicity is used. -/
theorem pairedCoefficient_mono {β L₀ L : ℝ} (hβ : β < 1)
    (hL₀ : 0 < L₀) (hL : L₀ ≤ L) :
    pairedCoefficient β L ≤ pairedCoefficient β L₀ := by
  have hLp : 0 < L := hL₀.trans_le hL
  have hbp : 0 ≤ 1 - β := by linarith
  have hp := Real.pi_pos
  unfold pairedCoefficient
  gcongr

/-- Uniform paired fixed-strip envelope with a caller-supplied evaluated coefficient.
All numerical dependence is isolated in pairedCoefficient beta L0 <= C. -/
theorem paired_envelope_of_coefficient {β L₀ C x : ℝ}
    (hβ : (7 / 8 : ℝ) ≤ β) (hβ' : β < 1) (hL₀ : 0 < L₀)
    (hR₀ : 16 ≤ (1 - β) * L₀) (hx : exp L₀ ≤ x)
    (hcoef : pairedCoefficient β L₀ ≤ C) :
    pairedErrorBound (x ^ (1 - β)) β x ≤ C * log x ^ 2 * x ^ (β - 1) := by
  have ha : 0 < 1 - β := by linarith
  have ha' : 1 - β ≤ 1 / 2 := by linarith
  have hx0 : 0 < x := (exp_pos L₀).trans_le hx
  have hL : L₀ ≤ log x := by
    have hh := log_le_log (exp_pos L₀) hx
    simpa using hh
  have hLp : 0 < log x := hL₀.trans_le hL
  have hxbase : exp (16 / (1 - β)) ≤ x := by
    apply (exp_le_exp.mpr ((div_le_iff₀ ha).mpr (by nlinarith [hR₀]))).trans hx
  have hx1 : 1 ≤ x := by linarith [add_one_le_exp L₀]
  set T := x ^ (1 - β) with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hTe : T = exp ((1 - β) * log x) := by
    rw [hT, rpow_def_of_pos hx0]; congr 1; ring
  have hlogT : log T = (1 - β) * log x := by rw [hTe, log_exp]
  have hR : 16 ≤ (1 - β) * log x := by
    exact hR₀.trans (mul_le_mul_of_nonneg_left hL ha.le)
  have hTlo : (1000000 : ℝ) ≤ T := by
    have he := (CH2Section7A.exp_nat_bounds 16).1
    have h16 : (1000000 : ℝ) ≤ exp 16 := by norm_num at he; linarith
    exact h16.trans (by rw [hTe]; exact exp_le_exp.mpr hR)
  have h1 : x ^ β * T = x := by
    rw [hT, ← rpow_add hx0]; convert rpow_one x using 1 <;> ring
  have h2 : x ^ (1 - β) * T = x * x ^ (1 - 2 * β) := by
    calc
      _ = x ^ ((1 - β) + (1 - β)) := by rw [hT, ← rpow_add hx0]
      _ = x ^ (1 + (1 - 2 * β)) := by congr 1; ring
      _ = x ^ (1 : ℝ) * x ^ (1 - 2 * β) := rpow_add hx0 _ _
      _ = _ := by rw [rpow_one]
  have hscale : ((x ^ β + x ^ (1 - β)) / (2 * x)) * T =
      (1 + x ^ (1 - 2 * β)) / 2 := by
    calc
      _ = (x ^ β * T + x ^ (1 - β) * T) / (2 * x) := by ring
      _ = (x + x * x ^ (1 - 2 * β)) / (2 * x) := by rw [h1,h2]
      _ = _ := by field_simp
  have hinv : x ^ (β - 1) = 1 / T := by
    rw [show β - 1 = -(1 - β) by ring, rpow_neg hx0.le, ← hT, one_div]
  have hq : x ^ (1 - 2 * β) ≤ (1 : ℝ) / 1000000 := by
    have hh := rpow_le_rpow_of_exponent_le hx1
      (show 1 - 2 * β ≤ β - 1 by linarith)
    rw [hinv] at hh
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) hTlo)
  have hspec0 : 0 ≤ spectralBound T := by
    unfold spectralBound
    rw [hlogT]
    positivity
  have hspec : spectralBound T * ((x ^ β + x ^ (1 - β)) / (2 * x)) * T ≤
      (500001 / 1000000 : ℝ) * spectralBound T := by
    rw [mul_assoc, hscale]
    have hm := mul_le_mul_of_nonneg_left
      (show (1 + x ^ (1 - 2 * β)) / 2 ≤ (500001 / 1000000 : ℝ) by linarith) hspec0
    nlinarith
  have hrem := scaled_remainder_fixed_strip ha ha' hxbase
  have hc := (pairedCoefficient_mono hβ' hL₀ hL).trans hcoef
  have hscaled : pairedErrorBound T β x * T ≤ pairedCoefficient β (log x) * log x^2 := by
    rw [pairedError_eq, add_mul]
    have heq : (16 / 5 : ℝ) + (500001 / 1000000) * spectralBound T =
        pairedCoefficient β (log x) * log x^2 := by
      unfold pairedCoefficient spectralBound
      rw [hlogT]
      field_simp
      ring
    linarith
  have hfinal := hscaled.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg (log x)))
  rw [hinv, mul_one_div]
  exact (le_div_iff₀ hT0).mpr hfinal

#print axioms paired_envelope_of_coefficient
end WinnerBetaA
