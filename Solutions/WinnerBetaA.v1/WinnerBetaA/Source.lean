/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Numerical

namespace WinnerBetaA
open Real IEANTN CH2QRH

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

/-- Actual source theorem with a reusable, explicitly numerical coefficient obligation. -/
theorem psi_paired_of_coefficient {β L₀ C : ℝ} (hβ : (7/8 : ℝ) ≤ β) (hβ' : β < 1)
    (hL₀ : 0 < L₀) (hR₀ : 16 ≤ (1 - β) * L₀)
    (hfree : ZetaZeroFreeHalfPlane β) (hcoef : pairedCoefficient β L₀ ≤ C) :
    HasPowerLogBound Eψ C 2 β (exp L₀) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L₀).trans_le hx
  have hL : L₀ ≤ log x := by
    have hh := log_le_log (exp_pos L₀) hx
    simpa using hh
  have ha : 0 < 1 - β := by linarith
  have hLpos : 0 < log x := hL₀.trans_le hL
  have hR : 16 ≤ (1 - β) * log x :=
    hR₀.trans (mul_le_mul_of_nonneg_left hL ha.le)
  have hL16 : 16 ≤ log x := by nlinarith [mul_nonneg (sub_nonneg.mpr hβ) hLpos.le]
  have h16 : (1000000 : ℝ) ≤ exp 16 := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    norm_num at hh
    linarith
  have hxnum : 1000000 ≤ x := by
    rw [← exp_log hx0]
    exact h16.trans (exp_le_exp.mpr hL16)
  have hTe : x ^ (1 - β) = exp ((1 - β) * log x) := by
    rw [rpow_def_of_pos hx0]
    congr 1
    ring
  have hT : 2000 ≤ x ^ (1 - β) := by
    rw [hTe]
    have hh := h16.trans (exp_le_exp.mpr hR)
    linarith
  have hRlog : 16 ≤ log (x ^ (1 - β)) := by rw [hTe, log_exp]; exact hR
  have hp := paired_finite_transfer hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hT hRlog hxnum (by linarith) hfree
  exact hp.trans (paired_envelope_of_coefficient hβ hβ' hL₀ hR₀ hx hcoef)

/-- This concrete actual psi theorem materially consumes the newly executed coefficient provider. -/
theorem psi_numerical_nine_tenths_200 (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    HasPowerLogBound Eψ (14554/10000000) 2 (9/10) (exp 200) :=
  psi_paired_of_coefficient hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfree Numerical.coefficient_200

theorem psi_numerical_nine_tenths_240 (hfree : ZetaZeroFreeHalfPlane (9/10)) :
    HasPowerLogBound Eψ (13344/10000000) 2 (9/10) (exp 240) :=
  psi_paired_of_coefficient hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfree Numerical.coefficient_240

theorem psi_numerical_seven_eighths_200 (hfree : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ (2048/1000000) 2 (7/8) (exp 200) :=
  psi_paired_of_coefficient hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfree Numerical.coefficient_seven_eighths

theorem psi_numerical_seven_eighths_240 (hfree : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ (19027/10000000) 2 (7/8) (exp 240) :=
  psi_paired_of_coefficient hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfree Numerical.coefficient_seven_eighths_240

end NamedInputs
#print axioms psi_numerical_nine_tenths_200
#print axioms psi_numerical_nine_tenths_240
end WinnerBetaA
