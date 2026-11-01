/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedNumerical
import PsiToTheta
import IEANTN.Nodes.QRHCH2.v4.Conclusions
import IEANTN.Nodes.CH2.v8.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

open Real

theorem QRHCH2.v4.challenge_psi_paired_bound
    (ch2_v8_paired_transfer : CH2.v8.paired_transfer)
    (openaiqrh_v1_zeta_seven_eighths : OpenAIQRH.v1.zeta_seven_eighths) :
    QRHCH2.v4.psi_paired_bound := ch2_v8_paired_transfer openaiqrh_v1_zeta_seven_eighths

theorem QRHCH2.v4.challenge_psi_numerical_bound
    (qrhch2_v4_psi_paired_bound : QRHCH2.v4.psi_paired_bound) : QRHCH2.v4.psi_numerical_bound := by
  intro x hx
  have h128 : Real.exp 128 ≤ x := (Real.exp_le_exp.mpr (by norm_num : (128 : ℝ) ≤ 300)).trans hx
  exact (qrhch2_v4_psi_paired_bound x h128).trans (CH2QRH.paired_power_numerical hx)

theorem QRHCH2.v4.challenge_theta_numerical_bound
    (qrhch2_v4_psi_numerical_bound : QRHCH2.v4.psi_numerical_bound) : QRHCH2.v4.theta_numerical_bound := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hp := qrhch2_v4_psi_numerical_bound x hx
  have hc := CH2QRH.psi_theta_correction_le hx
  have ht := FKS2Sol.Etheta_le_Epsi_add hx0
  norm_num at hp hc ⊢
  linarith

theorem QRHCH2.v4.challenge_short_prime_interval
    (qrhch2_v4_theta_numerical_bound : QRHCH2.v4.theta_numerical_bound)
    (primeinterval_v1_etheta_criterion : PrimeInterval.v1.eTheta_criterion) : QRHCH2.v4.short_prime_interval := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hh : 0 < x / 40000000000000 := by positivity
  apply primeinterval_v1_etheta_criterion x (x / 40000000000000) hx0 hh
  have h1 := mul_le_mul_of_nonneg_left (qrhch2_v4_theta_numerical_bound x hx) hx0.le
  have h2 := mul_le_mul_of_nonneg_left
    (qrhch2_v4_theta_numerical_bound (x + x / 40000000000000) (by linarith))
    (show 0 ≤ x + x / 40000000000000 by positivity)
  norm_num at h1 h2 ⊢
  linarith
