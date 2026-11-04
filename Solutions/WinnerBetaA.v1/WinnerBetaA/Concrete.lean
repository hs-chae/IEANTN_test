/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.SplitPi
import WinnerBetaA.Restricted

namespace WinnerBetaA
open Real IEANTN

section NamedInputs
variable (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH

theorem theta_numerical_nine_tenths_200 (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    HasPowerLogBound Eθ (1455400001/1000000000000) 2 (9/10) (exp 200) := by
  have hp := psi_numerical_nine_tenths_200 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  convert theta_from_large_psi_log2 (by norm_num : (7/8 : ℝ) ≤ 9/10)
    (by norm_num : (200 : ℝ) ≤ 200) hp using 1 <;> norm_num

theorem theta_numerical_nine_tenths_240 (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    HasPowerLogBound Eθ (1334400001/1000000000000) 2 (9/10) (exp 240) := by
  have hp := psi_numerical_nine_tenths_240 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  convert theta_from_large_psi_log2 (by norm_num : (7/8 : ℝ) ≤ 9/10)
    (by norm_num : (200 : ℝ) ≤ 240) hp using 1 <;> norm_num

theorem theta_numerical_seven_eighths_200 (hfree : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (2048000001/1000000000000) 2 (7/8) (exp 200) := by
  have hp := psi_numerical_seven_eighths_200 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  convert theta_from_large_psi_log2 (by norm_num : (7/8 : ℝ) ≤ 7/8)
    (by norm_num : (200 : ℝ) ≤ 200) hp using 1 <;> norm_num

theorem theta_numerical_seven_eighths_240 (hfree : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (1902700001/1000000000000) 2 (7/8) (exp 240) := by
  have hp := psi_numerical_seven_eighths_240 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  convert theta_from_large_psi_log2 (by norm_num : (7/8 : ℝ) ≤ 7/8)
    (by norm_num : (200 : ℝ) ≤ 240) hp using 1 <;> norm_num

/-- A new executed coefficient instance is carried all the way to actual prime-counting error. -/
theorem pi_numerical_nine_tenths (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    HasPowerLogBound Eπ (671/500000) 2 (9/10) (exp 240) := by
  have hA := theta_numerical_nine_tenths_200 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  have hB := theta_numerical_nine_tenths_240 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  apply pi_log2_two_profiles (a := (200 : ℝ)) (b := (240 : ℝ))
    (δ := (1/(2:ℝ)^16)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ _ hA hB
  · convert DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 16 using 1 <;> norm_num
  · norm_num

/-- Second genuine theorem input, with the same executable syntax and analytic pipeline.
This theorem separately requires the stronger boundary; it is never used in the restricted proof. -/
theorem pi_numerical_seven_eighths (hfree : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (957/500000) 2 (7/8) (exp 240) := by
  have hA := theta_numerical_seven_eighths_200 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  have hB := theta_numerical_seven_eighths_240 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  apply pi_log2_two_profiles (a := (200 : ℝ)) (b := (240 : ℝ))
    (δ := ((10/27:ℝ)^10)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ _ hA hB
  · convert QRHPropagation.exp_neg_nat_upper 10 using 1 <;> norm_num
  · norm_num

/-- Explicit improvement over the prior conservative restricted transfer on the matched ray.
This compares two proved allowances; no strongest-portfolio claim is made. -/
theorem pi_numerical_nine_tenths_improves_coarse (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    (∀ x ≥ exp (240 : ℝ), Eπ x ≤ (671/500000 : ℝ)*log x^2*x^((9/10 : ℝ)-1)) ∧
      (∀ x ≥ exp (240 : ℝ),
        (671/500000 : ℝ)*log x^2*x^((9/10 : ℝ)-1) <
          (21/1000 : ℝ)*log x^2*x^((9/10 : ℝ)-1)) := by
  refine ⟨pi_numerical_nine_tenths hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree, ?_⟩
  intro x hx
  have hx0 : 0 < x := (exp_pos (240 : ℝ)).trans_le hx
  have hl : 0 < log x := by
    apply log_pos
    have hh := add_one_le_exp (240 : ℝ)
    linarith
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right (by norm_num : (671/500000 : ℝ) < 21/1000) (pow_pos hl 2))
    (rpow_pos_of_pos hx0 _)

end NamedInputs
#print axioms pi_numerical_nine_tenths
#print axioms pi_numerical_seven_eighths
set_option pp.proofs false in
#print pi_numerical_nine_tenths
end WinnerBetaA
