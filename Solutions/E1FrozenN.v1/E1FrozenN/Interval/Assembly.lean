/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Interval.DensityReduction
import E1FrozenN.Interval.PrimeConsumer

namespace E1FrozenN.Interval
open Real Set MeasureTheory Complex WinnerDirectKernel
set_option maxHeartbeats 0

/-- The exact source adapter's minimum weights are consumed by the actual-zero
CDF theorem, with the common CHJ height contained in the enclosing height V. -/
theorem positive_budget_le_profile
    (hrvm : ZeroCount.v1.rvm_error_bound) (hFKS : FKS.v3.density_0618)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L Tstar : ℝ} (hL : 330 ≤ L) (hTstar : Tstar ≤ V L) :
    positiveZeroBudget (Real.exp L) (Real.exp (4*L/5)) Tstar ≤
      Real.exp (4*L/5)*(low L+high L) := by
  classical
  let S := positiveZeros Tstar
  have hS : ∀ rho ∈ S, rho ∈ IEANTN.zetaZeroesIn Set.univ (Ioc 0 (V L)) := by
    intro rho hr
    have hm := positive_mem hr
    exact ⟨trivial,⟨hm.2.1.1,hm.2.1.2.trans hTstar⟩,hm.2.2⟩
  have hb := clipped_density_layer_exp_bound hrvm hFKS hQRH S hL hS
  have hU0 : 0 < U L := lt_of_lt_of_le (by norm_num) (U_ge_height hL)
  have hδU : (Real.exp (4*L/5)/Real.exp L)*U L=k := by
    rw [gap_ratio]
    unfold delta U
    calc _ = k*(Real.exp (-L/5)*Real.exp (L/5)) := by ring
         _ = k := by
           rw [←Real.exp_add,show -L/5+L/5=0 by ring,Real.exp_zero,mul_one]
  have hK : 2+Real.exp (4*L/5)/Real.exp L ≤ k := by
    rw [gap_ratio]
    exact two_add_delta_le_k hL
  have hmin : ∀ rho ∈ S,
      min (Real.exp (4*L/5)/Real.exp L)
        ((2+Real.exp (4*L/5)/Real.exp L)/rho.im) ≤ k/max (U L) rho.im := by
    intro rho hr
    exact min_le_clipped_reciprocal hU0 (hS rho hr).2.1.1 hδU hK
  have hm : positiveZeroBudget (Real.exp L) (Real.exp (4*L/5)) Tstar ≤
      2*∑ rho ∈ S, (IEANTN.zetaOrder rho:ℝ)*(Real.exp L)^rho.re*
        (k/max (U L) rho.im) := by
    unfold positiveZeroBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro rho hr
    have hw := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self (hS rho hr)
    exact mul_le_mul_of_nonneg_left (hmin rho hr) (mul_nonneg hw (by positivity))
  have he : 2*∑ rho ∈ S, (IEANTN.zetaOrder rho:ℝ)*(Real.exp L)^rho.re*
      (k/max (U L) rho.im) =
      Real.exp (4*L/5)*(2*U L*(∑ rho ∈ S,
        ((IEANTN.zetaOrder rho:ℝ)/max (U L) rho.im)*Real.exp (-(1-rho.re)*L))) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hr
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    have hexp : Real.exp (4*L/5)*U L*Real.exp (-(1-rho.re)*L)=
        k*Real.exp (L*rho.re) := by
      unfold U
      calc _ = k*(Real.exp (4*L/5)*Real.exp (L/5)*Real.exp (-(1-rho.re)*L)) := by ring
           _ = _ := by repeat rw [←Real.exp_add];congr 1;congr 1;ring
    calc _ = 2*((IEANTN.zetaOrder rho:ℝ)/max (U L) rho.im)*(k*Real.exp (L*rho.re)) := by ring
         _ = _ := by rw [←hexp];ring
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)

/-- The actual psi increment retains the entire high/low allowance functions.
This supports strict quantitative comparisons when a numerical program improves
the high component, without identifying that gain with a Boolean prime claim. -/
theorem psi_increment_error_profile
    (hsource : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : 330 ≤ L) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)| ≤ (low L+high L+49/1000)*Real.exp (4*L/5) := by
  have hdom := truncation_domain hL
  obtain ⟨Tstar,hTlo,hThi,herr⟩ := chjii_to_positive_budget hsource hQRH
    (Real.exp_le_exp.mpr (by linarith : (40:ℝ)≤L)) (Real.exp_pos (4*L/5)).le
    hdom.1 hdom.2
  have hstar : Tstar ≤ V L := by simpa only [V] using hThi
  have hbudget := positive_budget_le_profile hrvm hFKS hQRH hL hstar
  have htrunc := truncation_error_bound hL
  rw [Real.log_exp] at herr
  nlinarith

/-- Relative error of an interval psi increment, normalized by its length.
This is a different mathematical object from the PNT error Epsi. -/
theorem psi_increment_relative_profile
    (hsource : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : 330 ≤ L) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)|/Real.exp (4*L/5) ≤ low L+high L+49/1000 := by
  exact (div_le_iff₀ (Real.exp_pos _)).mpr
    (psi_increment_error_profile hsource hFKS hrvm hQRH hL)

/-- A quantitative theta increment is also a real consumer of the improved
high-density calculation. The additional 1/1000 is Mathlib's prime-power bound. -/
theorem theta_increment_lower_profile
    (hsource : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : 330 ≤ L) :
    (1-(low L+high L+50/1000))*Real.exp (4*L/5) ≤
      Chebyshev.theta (Real.exp L+Real.exp (4*L/5))-Chebyshev.theta (Real.exp L) := by
  have hpsi := (abs_le.mp (psi_increment_error_profile hsource hFKS hrvm hQRH hL)).1
  have hpp := prime_power_error_bound hL
  have hx := Chebyshev.theta_le_psi (Real.exp L)
  nlinarith

/-- Generic assembly: the high and low profile bounds are mathematical helper
premises here; the final numerical endpoint must discharge them separately. -/
theorem psi_increment_error_of_budgets
    (hsource : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L : ℝ} (hL : 330 ≤ L) (hhigh : high L ≤ 36/100) (hlow : low L ≤ 1/1000) :
    |Chebyshev.psi (Real.exp L+Real.exp (4*L/5))-Chebyshev.psi (Real.exp L)-
      Real.exp (4*L/5)| ≤ (41/100:ℝ)*Real.exp (4*L/5) := by
  have hdom := truncation_domain hL
  obtain ⟨Tstar,hTlo,hThi,herr⟩ := chjii_to_positive_budget hsource hQRH
    (Real.exp_le_exp.mpr (by linarith : (40:ℝ)≤L)) (Real.exp_pos (4*L/5)).le
    hdom.1 hdom.2
  have hstar : Tstar ≤ V L := by simpa only [V] using hThi
  have hbudget := positive_budget_le_profile hrvm hFKS hQRH hL hstar
  have htrunc := truncation_error_bound hL
  rw [Real.log_exp] at herr
  have hsum : low L+high L ≤ (361/1000:ℝ) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (4*L/5)).le
  nlinarith

/-- Full real ray with only the four original mathematical source premises and
explicit generic profile helpers. The concrete final result supplies the two
helpers from the numerical-program and full-range theorems. -/
theorem prime_ray_of_budgets
    (hsource : CHJII_Theorem1_3_Row40)
    (hFKS : FKS.v3.density_0618) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hQRH : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hhigh : ∀ L : ℝ, 330 ≤ L → high L ≤ 36/100)
    (hlow : ∀ L : ℝ, 330 ≤ L → low L ≤ 1/1000) :
    ∀ x : ℝ, Real.exp 330 ≤ x → IEANTN.HasPrimeInInterval x (x^(4/5:ℝ)) := by
  apply real_ray_of_log_ray
  intro L hL
  apply hasPrime_exp_of_psi_error hL
    (psi_increment_error_of_budgets hsource hFKS hrvm hQRH hL (hhigh L hL) (hlow L hL))
  norm_num

#print axioms positive_budget_le_profile
#print axioms psi_increment_relative_profile
#print axioms theta_increment_lower_profile
#print axioms psi_increment_error_of_budgets
#print axioms prime_ray_of_budgets
end E1FrozenN.Interval
