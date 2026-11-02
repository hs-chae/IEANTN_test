/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RefinedResult

/-! Retain the polynomial before Phase1 rounded it into one quadratic coefficient. -/
namespace QRHPhase2
open Real IEANTN CH2.v7 CH2QRH

theorem paired_polynomial_bound {x : ℝ} (hx : exp 128 ≤ x) :
    pairedErrorBound (x ^ ((1 : ℝ) / 8)) (7 / 8) x ≤
      ((797 / 640000 : ℝ) * log x ^ 2 + (29 / 200) * log x + 16 / 5) *
        x ^ (-(1 : ℝ) / 8) := by
  have hx0 : 0 < x := (Real.exp_pos (128 : ℝ)).trans_le hx
  have hL : 128 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (128 : ℝ)) hx
    simpa using hh
  have hx1 : 1 ≤ x := by
    have hh := Real.add_one_le_exp (128 : ℝ)
    linarith
  set R := Real.log x / 8 with hR
  set T := x ^ ((1 : ℝ) / 8) with hT
  have hR16 : 16 ≤ R := by dsimp [R]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hTe : T = Real.exp R := by
    rw [hT, Real.rpow_def_of_pos hx0, hR]
    congr 1
    ring
  have hT0 : 0 < T := by rw [hTe]; positivity
  have hTlo : (1000000 : ℝ) ≤ T := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    exact h16.trans (by rw [hTe]; exact Real.exp_le_exp.mpr hR16)
  have hlogT : Real.log T = R := by rw [hTe, Real.log_exp]
  have h1 : x ^ ((7 : ℝ) / 8) * T = x := by
    rw [hT, ← Real.rpow_add hx0]
    norm_num
  have h2 : x ^ (1 - (7 : ℝ) / 8) * T = x * x ^ (-(3 : ℝ) / 4) := by
    calc _ = x ^ ((1 : ℝ) / 4) := by rw [hT, ← Real.rpow_add hx0]; norm_num
      _ = x ^ (1 : ℝ) * x ^ (-(3 : ℝ) / 4) := by rw [← Real.rpow_add hx0]; norm_num
      _ = _ := by rw [Real.rpow_one]
  have hscale : ((x ^ ((7 : ℝ) / 8) + x ^ (1 - (7 : ℝ) / 8)) / (2 * x)) * T =
      (1 + x ^ (-(3 : ℝ) / 4)) / 2 := by
    field_simp
    nlinarith
  have hinv : x ^ (-(1 : ℝ) / 8) = 1 / T := by
    rw [show -(1 : ℝ) / 8 = -(1 / 8 : ℝ) by ring, Real.rpow_neg hx0.le, ← hT, one_div]
  have hq : x ^ (-(3 : ℝ) / 4) ≤ (1 : ℝ) / 1000000 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : -(3 : ℝ) / 4 ≤ -1 / 8)
    rw [hinv] at hh
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) hTlo)
  have hC0 : 0 ≤ spectralBound T := by unfold spectralBound; rw [hlogT]; positivity
  have hCup : spectralBound T ≤ 0.1593 * R ^ 2 + 2.319 * R := by
    unfold spectralBound
    rw [hlogT]
    have hp := Real.pi_pos
    have hp2 := Real.pi_gt_d2
    have hcoef : 1 / (2 * Real.pi) ≤ (0.1593 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hcoef2 : 2 + 1 / Real.pi ≤ (2.319 : ℝ) := by
      have hh : 1 / Real.pi ≤ (0.319 : ℝ) := by rw [div_le_iff₀ hp]; linarith
      linarith
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg R)
    have hh2 := mul_le_mul_of_nonneg_right hcoef2 hR0
    rw [one_div_mul_eq_div] at hh
    linarith
  have hspec : spectralBound T * ((x ^ ((7 : ℝ) / 8) + x ^ (1 - (7 : ℝ) / 8)) / (2 * x)) * T ≤
      0.0797 * R ^ 2 + 1.16 * R := by
    rw [mul_assoc, hscale]
    have hh := mul_le_mul_of_nonneg_left (show (1 + x ^ (-(3 : ℝ) / 4)) / 2 ≤
      (0.500001 : ℝ) by linarith) hC0
    have hh2 := mul_le_mul_of_nonneg_right hCup (by norm_num : (0 : ℝ) ≤ 0.500001)
    nlinarith [sq_nonneg R]
  have hrem := scaled_remainder_le ((Real.exp_le_exp.mpr (by norm_num : (128 : ℝ) ≤ 128)).trans hx)
  have hb : pairedErrorBound T (7 / 8) x * T ≤
      (3.2 : ℝ) + 0.0797 * R ^ 2 + 1.16 * R := by
    rw [pairedError_eq, add_mul]
    linarith
  rw [hinv, mul_one_div]
  apply (le_div_iff₀ hT0).mpr
  calc
    _ ≤ (3.2 : ℝ) + 0.0797 * R ^ 2 + 1.16 * R := hb
    _ = _ := by dsimp [R]; ring

/-- The original13source inputs suffice; no new analytic transfer is assumed. -/
theorem psi_polynomial_transfer (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions) :
    ZetaZeroFreeHalfPlane (7 / 8) → ∀ x : ℝ, exp 128 ≤ x →
      Eψ x ≤ ((797 / 640000 : ℝ) * log x ^ 2 + (29 / 200) * log x + 16 / 5) *
        x ^ (-(1 : ℝ) / 8) := by
  intro hqrh x hx
  have hx0 : 0 < x := (Real.exp_pos (128 : ℝ)).trans_le hx
  have hL : 128 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (128 : ℝ)) hx
    simpa using hh
  have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    norm_num at hh
    linarith
  have hxnum : 1000000 ≤ x := h16.trans ((Real.exp_le_exp.mpr (by norm_num : (16 : ℝ) ≤ 128)).trans hx)
  have hTexp : x ^ ((1 : ℝ) / 8) = Real.exp (Real.log x / 8) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hT : 2000 ≤ x ^ ((1 : ℝ) / 8) := by
    have hh : Real.exp 16 ≤ x ^ ((1 : ℝ) / 8) := by
      rw [hTexp]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hR : 16 ≤ Real.log (x ^ ((1 : ℝ) / 8)) := by rw [hTexp, Real.log_exp]; linarith
  exact (paired_finite_transfer hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    hT hR hxnum (by linarith) hqrh).trans (paired_polynomial_bound hx)


/-- Strictly smaller than the actual Phase1 denominator566envelope on its entire range. -/
theorem polynomial_strictly_improves {x : ℝ} (hx : exp 300 ≤ x) :
    ((797 / 640000 : ℝ) * log x ^ 2 + (29 / 200) * log x + 16 / 5) *
        x ^ (-(1 : ℝ) / 8) <
      (1 / 566 : ℝ) * log x ^ 2 * x ^ (-(1 : ℝ) / 8) := by
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hL : 300 ≤ log x := by
    have h := log_le_log (exp_pos (300 : ℝ)) hx
    simpa only [log_exp] using h
  have hpoly : (797 / 640000 : ℝ) * log x ^ 2 + (29 / 200) * log x + 16 / 5 <
      (1 / 566 : ℝ) * log x ^ 2 := by
    nlinarith [sq_nonneg (log x - 300)]
  exact mul_lt_mul_of_pos_right hpoly (rpow_pos_of_pos hx0 _)

end QRHPhase2
