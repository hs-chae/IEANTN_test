/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PrimeIntervalReplay
import PairedConsumer

/-! Replay the entire new chain using the original, unchanged PrimeInterval solution.
Only the original named source statements and OpenAI QRH are assumptions. Neither the
new analytic transfer nor the PNT/theta/prime-interval conclusions are assumed here. -/

theorem QRHCH2PairedReplay.improved_prime_intervals (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths) :
    QRHCH2.v4.psi_numerical_bound ∧ QRHCH2.v4.theta_numerical_bound ∧
      QRHCH2.v4.short_prime_interval := by
  have htransfer : CH2.v8.paired_transfer :=
    CH2QRH.paired_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH
  have hpower := QRHCH2.v4.challenge_psi_paired_bound htransfer hqrh
  have hpsi := QRHCH2.v4.challenge_psi_numerical_bound hpower
  have htheta := QRHCH2.v4.challenge_theta_numerical_bound hpsi
  have hinterval := QRHCH2.v4.challenge_short_prime_interval htheta
    PrimeInterval.v1.challenge_eTheta_criterion
  exact ⟨hpsi, htheta, hinterval⟩

/-- The old displayed CH2 allowance is too large to satisfy the existing criterion at
this new interval width. This compares the allowances, not the truth of prime existence. -/
theorem QRHCH2PairedReplay.old_allowance_fails_new_interval {x : ℝ} (hx : 0 < x) :
    x / 40000000000000 ≤
      x * (Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt x) +
      (x + x / 40000000000000) *
        (Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt (x + x / 40000000000000)) := by
  have hp := Real.pi_gt_three
  have h0 : 0 ≤ (113.67 : ℝ) / Real.sqrt x := by positivity
  have h1 : 0 ≤ (113.67 : ℝ) / Real.sqrt (x + x / 40000000000000) := by positivity
  have hb : (1 : ℝ) / 10 ^ 12 ≤ Real.pi / (3 * (10 : ℝ) ^ 12) := by
    norm_num
    linarith
  have hx1 : 0 ≤ x + x / 40000000000000 := by positivity
  have ha := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 10 ^ 12 ≤
    Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt x by linarith) hx.le
  have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 10 ^ 12 ≤
    Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt (x + x / 40000000000000) by linarith) hx1
  norm_num at ha hc ⊢
  linarith
