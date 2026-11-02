/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Toolkit
import FKS2Correction.PrimeCriterion

namespace FKS2Correction
open Real IEANTN

noncomputable def Uold : ℝ := 121.096 * (1 + (11 : ℝ) / 10 ^ 62)
noncomputable def commonShape (L : ℝ) : ℝ :=
  (L / 5.5666305) ^ ((3 : ℝ) / 2) * exp (-2 * sqrt (L / 5.5666305))

theorem provided_proposition13 : FKS2.v2.proposition_13 := by
  exact fun _ _ _ _ _ _ _ hR hA hB hx ha hb hc hp =>
    FKS2Sol.classicalBound_theta_of_psi hR hA hB hx ha hb hc hp

theorem anchor_nonnegative : 0 ≤ BKLNW.v1.a₂ 30 := by
  exact FKS2Sol.BKLNW_a₂_nonneg

theorem anchor_comparison (hB : BKLNW.v1.corollary_5_1) :
    ∀ x ≥ exp 30, Chebyshev.psi x - Chebyshev.theta x ≤
      (1 + 1.93378e-8) * x ^ ((1 : ℝ) / 2) +
        BKLNW.v1.a₂ 30 * x ^ ((1 : ℝ) / 3) := by
  intro x hx
  exact (hB 30 (by norm_num) (by nlinarith [FKS2Sol.one_le_log_ten]) x hx).le

theorem comparison_at_threshold {L : ℝ} (hL : 30 ≤ L)
    (hB : BKLNW.v1.corollary_5_1) :
    ∀ x ≥ exp L, Chebyshev.psi x - Chebyshev.theta x ≤
      (1 + 1.93378e-8) * x ^ ((1 : ℝ) / 2) +
        BKLNW.v1.a₂ 30 * x ^ ((1 : ℝ) / 3) := by
  intro x hx
  exact anchor_comparison hB x ((exp_le_exp.mpr hL).trans hx)

theorem comparison_from_anchor (hB : BKLNW.v1.corollary_5_1) :
    ∀ x ≥ exp 300, Chebyshev.psi x - Chebyshev.theta x ≤
      (1 + 1.93378e-8) * x ^ ((1 : ℝ) / 2) +
        BKLNW.v1.a₂ 30 * x ^ ((1 : ℝ) / 3) := by
  exact comparison_at_threshold (by norm_num) hB

theorem common_shape_tail {L : ℝ} (hL : 300 ≤ L) : commonShape L ≤ 1 / 4000 := by
  have hs : (7.3 : ℝ) ≤ sqrt (L / 5.5666305) := by
    apply le_sqrt_of_sq_le
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 5.5666305)]
    nlinarith
  have hp := poly_exp_decreasing 3 (L0 := (7.3 : ℝ)) (c := 2)
    (by norm_num) (by norm_num) hs
  have he : exp (-(14.6 : ℝ)) ≤ (10/27 : ℝ)^14 * (5/8) := by
    have hf : exp (-(0.6 : ℝ)) ≤ (5/8 : ℝ) := by
      rw [exp_neg, ← one_div]
      have h := add_one_le_exp (0.6 : ℝ)
      apply (div_le_iff₀ (exp_pos _)).mpr
      nlinarith
    calc
      _ = exp (-(14 : ℝ)) * exp (-(0.6 : ℝ)) := by rw [← exp_add]; norm_num
      _ ≤ _ := mul_le_mul (exp_neg_nat_upper 14) hf (exp_pos _).le (by positivity)
  have hf : (7.3 : ℝ)^3 * ((10/27 : ℝ)^14 * (5/8)) ≤ 1/4000 := by norm_num
  have hfin : sqrt (L / 5.5666305)^3 * exp (-2 * sqrt (L / 5.5666305)) ≤
      (1/4000 : ℝ) := by
    calc
      _ ≤ (7.3 : ℝ)^3 * exp (-(14.6 : ℝ)) := by convert hp using 1 <;> norm_num
      _ ≤ _ := (mul_le_mul_of_nonneg_left he (by positivity)).trans hf
  unfold commonShape
  rw [rpow_div_two_eq_sqrt _ (by positivity)]
  norm_num at *
  exact hfin

/-- Fixed consumer shared by the baseline and the QRH update. -/
theorem theta_from_application {A nubar : ℝ} (hA : 0 < A)
    (hpsi : HasClassicalBound Eψ A (3/2) 2 5.5666305 (exp 300))
    (hB : BKLNW.v1.corollary_5_1)
    (hNumerics : FKS2Numerics.v3.nuStar A 300 ≤ nubar) :
    HasClassicalBound Eθ (A * (1+nubar)) (3/2) 2 5.5666305 (exp 300) := by
  have ht := provided_proposition13 A (3/2) 2 5.5666305
    (1+1.93378e-8) (BKLNW.v1.a₂ 30) (exp 300) (by norm_num) hA (by norm_num)
    (exp_le_exp.mpr (by norm_num)) (by norm_num) anchor_nonnegative
    (comparison_from_anchor hB) hpsi
  intro x hx
  have hx1 : 1 < x := by linarith [add_one_le_exp (300 : ℝ)]
  apply (ht x hx).trans
  apply FKS2Sol.admissibleBound_mono_A (by norm_num) hx1
  simpa [FKS2Numerics.v3.nuStar, add_comm] using
    mul_le_mul_of_nonneg_left (add_le_add_right hNumerics 1) hA.le

/-- The exact PrimeInterval criterion consumes the FKS2 output and the numerical provider. -/
theorem intervals_from_application {A nubar D : ℝ} (hA : 0 < A)
    (hU : 0 ≤ A * (1+nubar)) (hD : 0 < D)
    (hsmall : (2*D+1) * (A*(1+nubar)/4000) < 1)
    (hpsi : HasClassicalBound Eψ A (3/2) 2 5.5666305 (exp 300))
    (hB : BKLNW.v1.corollary_5_1)
    (hNumerics : FKS2Numerics.v3.nuStar A 300 ≤ nubar) :
    ∀ x ≥ exp 300, HasPrimeInInterval x (x/D) := by
  have htheta := theta_from_application hA hpsi hB hNumerics
  have hnum : HasNumericalBound Eθ (A*(1+nubar)/4000) (exp 300) := by
    intro y hy
    have hy0 : 0 < y := (exp_pos (300 : ℝ)).trans_le hy
    have hlog : 300 ≤ log y := by
      simpa using log_le_log (exp_pos (300 : ℝ)) hy
    calc
      Eθ y ≤ (A*(1+nubar)) * commonShape (log y) := by
        simpa [admissibleBound, commonShape, mul_assoc, Real.sqrt_eq_rpow] using htheta y hy
      _ ≤ (A*(1+nubar)) * (1/4000) :=
        mul_le_mul_of_nonneg_left (common_shape_tail hlog) hU
      _ = _ := by ring
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  have hh : 0 < x/D := div_pos hx0 hD
  have h1 := mul_le_mul_of_nonneg_left (hnum x hx) hx0.le
  have h2 := mul_le_mul_of_nonneg_left (hnum (x+x/D) (by linarith))
    (show 0 ≤ x+x/D by positivity)
  have hc : (2*x+x/D)*(A*(1+nubar)/4000) < x/D := by
    have ht := mul_lt_mul_of_pos_left hsmall hh
    convert ht using 1 <;> first | rfl | field_simp [hD.ne']
  exact PrimeInterval.v1.challenge_eTheta_criterion x (x/D) hx0 hh (by linarith)

theorem baseline_psi (hF : FKS.v2.psi_classical_bound) :
    HasClassicalBound Eψ 121.096 (3/2) 2 5.5666305 (exp 300) := by
  intro x hx
  exact hF x (by linarith [add_one_le_exp (300 : ℝ)])

theorem baseline_theta (hF : FKS.v2.psi_classical_bound)
    (hB : BKLNW.v1.corollary_5_1) :
    HasClassicalBound Eθ Uold (3/2) 2 5.5666305 (exp 300) := by
  exact theta_from_application (by norm_num) (baseline_psi hF) hB
    (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using baseline_provider)

theorem baseline_intervals (hF : FKS.v2.psi_classical_bound)
    (hB : BKLNW.v1.corollary_5_1) :
    ∀ x ≥ exp 300, HasPrimeInInterval x (x/16) := by
  exact intervals_from_application (A := 121.096) (nubar := (11 : ℝ)/10^62)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (baseline_psi hF) hB (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using baseline_provider)

end FKS2Correction
