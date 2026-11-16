/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RefinedResult
import PsiToTheta
import IEANTN.Nodes.QRHCH2.v5.Conclusions
import IEANTN.Nodes.CH2.v9.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v1.Conclusions

open Real

theorem QRHCH2.v5.challenge_psi_refined_bound
    (ch2_v9_refined_transfer : CH2.v9.refined_transfer)
    (openaiqrh_v1_zeta_seven_eighths : OpenAIQRH.v1.zeta_seven_eighths) :
    QRHCH2.v5.psi_refined_bound := ch2_v9_refined_transfer openaiqrh_v1_zeta_seven_eighths

theorem QRHCH2.v5.challenge_psi_numerical_bound
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound) : QRHCH2.v5.psi_numerical_bound := by
  intro x hx
  have h300 : Real.exp 300 ≤ x := (Real.exp_le_exp.mpr (by norm_num : (300 : ℝ) ≤ 300)).trans hx
  exact (qrhch2_v5_psi_refined_bound x h300).trans (CH2QRH.refined_power_numerical hx)

theorem QRHCH2.v5.challenge_theta_numerical_bound
    (qrhch2_v5_psi_numerical_bound : QRHCH2.v5.psi_numerical_bound) : QRHCH2.v5.theta_numerical_bound := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hp := qrhch2_v5_psi_numerical_bound x hx
  have hc := CH2QRH.psi_theta_correction_le hx
  have ht := FKS2Sol.Etheta_le_Epsi_add hx0
  norm_num at hp hc ⊢
  linarith

theorem QRHCH2.v5.challenge_short_prime_interval
    (qrhch2_v5_theta_numerical_bound : QRHCH2.v5.theta_numerical_bound)
    (primeinterval_v1_etheta_criterion : PrimeInterval.v1.eTheta_criterion) : QRHCH2.v5.short_prime_interval := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hh : 0 < x / 60000000000000 := by positivity
  apply primeinterval_v1_etheta_criterion x (x / 60000000000000) hx0 hh
  have h1 := mul_le_mul_of_nonneg_left (qrhch2_v5_theta_numerical_bound x hx) hx0.le
  have h2 := mul_le_mul_of_nonneg_left
    (qrhch2_v5_theta_numerical_bound (x + x / 60000000000000) (by linarith))
    (show 0 ≤ x + x / 60000000000000 by positivity)
  norm_num at h1 h2 ⊢
  linarith
