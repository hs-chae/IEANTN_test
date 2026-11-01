/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NumericEnvelope
import PsiToTheta
import IEANTN.Nodes.QRHCH2.v3.Conclusions
import IEANTN.Nodes.CH2.v7.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

open Real

theorem QRHCH2.v3.challenge_psi_numerical_bound
    (ch2_v7_finite_transfer : CH2.v7.finite_transfer)
    (openaiqrh_v1_zeta_seven_eighths : OpenAIQRH.v1.zeta_seven_eighths) : QRHCH2.v3.psi_numerical_bound := by
  intro x hx
  obtain ⟨hTlo, _, hXlo, _⟩ := CH2QRH.exp_bounds_36_300
  have hxnum : (1000000 : ℝ) ≤ x := by
    have hh := hXlo.trans hx
    norm_num at hh ⊢
    linarith
  have hxlog : 1 ≤ log x := by
    have hh := log_le_log (exp_pos (300 : ℝ)) hx
    rw [log_exp] at hh
    linarith
  exact (ch2_v7_finite_transfer (exp 36) x (7 / 8) (by linarith) (by norm_num) hxnum hxlog openaiqrh_v1_zeta_seven_eighths).trans
    (CH2QRH.finiteErrorBound_le_1573e_neg17 hx)

theorem QRHCH2.v3.challenge_theta_numerical_bound
    (qrhch2_v3_psi_numerical_bound : QRHCH2.v3.psi_numerical_bound) : QRHCH2.v3.theta_numerical_bound := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hp := qrhch2_v3_psi_numerical_bound x hx
  have hc := CH2QRH.psi_theta_correction_le hx
  have ht := FKS2Sol.Etheta_le_Epsi_add hx0
  norm_num at hp hc ⊢
  linarith

theorem QRHCH2.v3.challenge_short_prime_interval
    (qrhch2_v3_theta_numerical_bound : QRHCH2.v3.theta_numerical_bound)
    (primeinterval_v1_etheta_criterion : PrimeInterval.v1.eTheta_criterion) : QRHCH2.v3.short_prime_interval := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hh : 0 < x / 30000000000000 := by positivity
  apply primeinterval_v1_etheta_criterion x (x / 30000000000000) hx0 hh
  have h1 := mul_le_mul_of_nonneg_left (qrhch2_v3_theta_numerical_bound x hx) hx0.le
  have h2 := mul_le_mul_of_nonneg_left
    (qrhch2_v3_theta_numerical_bound (x + x / 30000000000000) (by linarith))
    (show 0 ≤ x + x / 30000000000000 by positivity)
  norm_num at h1 h2 ⊢
  linarith
