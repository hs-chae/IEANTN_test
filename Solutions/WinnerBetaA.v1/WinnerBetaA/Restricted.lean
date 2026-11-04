/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GeneralStrip
import WinnerBetaA.Theta
import WinnerBetaA.SharpPi

namespace WinnerBetaA
open Real IEANTN
open DudekPlattNumerics.v4.Numerics (exp_neg_nat_le)

section Restricted
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
    (hfree : ZetaZeroFreeHalfPlane (9 / 10))
include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hfree

/-- A real restricted-input zero-free-to-psi theorem, not a weakened known profile. -/
theorem psi_nine_tenths :
    HasPowerLogBound Eψ (1 / 50) 2 (9 / 10) (exp 160) := by
  have hg := CH2QRH.general_fixed_strip_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH
  intro x hx
  have hs := hg (9 / 10) (by norm_num) (by norm_num) hfree x
  norm_num at hs
  convert hs hx using 1 <;> norm_num

/-- The finite prime-power correction is derived, not imported from stronger QRH. -/
theorem theta_nine_tenths :
    HasPowerLogBound Eθ (2001 / 100000) 2 (9 / 10) (exp 160) := by
  have hslack : 2 * (160 : ℝ) * exp (-((9 / 10 : ℝ) - 1 / 2) * 160) ≤
      (1 / 100000 : ℝ) := by
    norm_num
    have he := exp_neg_nat_le 64
    norm_num only [Nat.cast_ofNat] at he
    calc
      _ ≤ 320 / (2 : ℝ)^64 := by linarith
      _ ≤ _ := by norm_num
  have hψ := psi_nine_tenths hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  convert theta_from_psi_log2 (C := (1 / 50 : ℝ)) (β := (9 / 10 : ℝ))
    (L₀ := (160 : ℝ)) (ε := (1 / 100000 : ℝ)) (by norm_num) (by norm_num)
    hslack hψ using 1 <;> norm_num

/-- An actual entire-ray Epi theorem under the restricted beta=9/10 interface.
Only the named CH2 ingredients and this weaker zero-free half-plane are consumed. -/
theorem pi_nine_tenths :
    HasPowerLogBound Eπ (21 / 1000) 2 (9 / 10) (exp 200) := by
  have hθ := theta_nine_tenths hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hfree
  intro x hx
  have hx0 : 0 < x := (exp_pos (200 : ℝ)).trans_le hx
  let L := log x
  have hL : 200 ≤ L := by
    have hh := log_le_log (exp_pos (200 : ℝ)) hx
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  have heq : exp L = x := exp_log hx0
  have hx160 : exp 160 ≤ exp L := exp_le_exp.mpr (by linarith)
  have hp := QRHPiPower.pi_power_transfer (A := (2001 / 100000 : ℝ))
    (β := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
    (show 2 ≤ exp 160 by linarith [add_one_le_exp (160 : ℝ)]) hx160 hθ
  rw [log_exp, rpow_def_of_pos (exp_pos L), log_exp] at hp
  have hid : L * ((9 / 10 : ℝ) - 1) = -L / 10 := by ring
  rw [hid] at hp
  have hearly : (4 * exp 160 + 3) * L / exp L ≤
      (7 / (2 : ℝ)^20) * L * exp (-L / 10) := by
    have h160 : 1 ≤ exp (160 : ℝ) := by linarith [add_one_le_exp (160 : ℝ)]
    have hex : exp (160 - 9 * L / 10) ≤ 1 / (2 : ℝ)^20 := by
      calc
        _ ≤ exp (-(20 : ℕ)) := exp_le_exp.mpr (by norm_num; linarith)
        _ ≤ _ := exp_neg_nat_le 20
    calc
      _ ≤ (7 * exp 160) * L / exp L := by gcongr; linarith
      _ = 7 * L * exp (-L / 10) * exp (160 - 9 * L / 10) := by
        rw [mul_assoc (7 * L), ← exp_add]
        rw [show -L / 10 + (160 - 9 * L / 10) = 160 - L from by ring, exp_sub]
        ring
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hex
          (show 0 ≤ 7 * L * exp (-L / 10) by positivity)
        nlinarith
  have hcoef : ((2001 / 100000 : ℝ) * L^2 + (2001 / 100000) / (9 / 10) * L) +
      (7 / (2 : ℝ)^20) * L ≤ (21 / 1000 : ℝ) * L^2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 200 by linarith)]
  have hfinal : Eπ (exp L) ≤ (21 / 1000 : ℝ) * L^2 * exp (-L / 10) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef (exp_pos (-L / 10)).le]
  rw [← heq, log_exp, rpow_def_of_pos (exp_pos L), log_exp, hid]
  exact hfinal

end Restricted

#print axioms psi_nine_tenths
#print axioms theta_nine_tenths
#print axioms pi_nine_tenths
set_option pp.proofs false in
#print pi_nine_tenths
end WinnerBetaA
