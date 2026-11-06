/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.DensityReduction
import E1NPlus.PrimeConsumer

namespace E1NPlus
open Real Set MeasureTheory WinnerDirectKernel
set_option maxHeartbeats 0

theorem positive_budget_le_profile
    (hrvm:ZeroCount.v1.rvm_error_bound)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L Tstar:ℝ} (hL:330 ≤ L) (hTstar:Tstar ≤ V L) :
    E1FrozenN.Interval.positiveZeroBudget (exp L) (gap L) Tstar ≤ gap L*(low L+high L) := by
  classical
  let S:=positiveZeros Tstar
  have hS:∀rho∈S,rho∈IEANTN.zetaZeroesIn Set.univ (Ioc 0 (V L)):=by
    intro rho hr
    have hm:=positive_mem hr
    exact ⟨trivial,⟨hm.2.1.1,hm.2.1.2.trans hTstar⟩,hm.2.2⟩
  have hb:=clipped_density_layer_exp_bound hrvm h8 hRH hQRH S hL hS
  have hU0:0<U L:=lt_of_lt_of_le (by norm_num) (U_ge_height hL)
  have hδU:(gap L/exp L)*U L=(2001/1000:ℝ):=by rw [gap_ratio];exact delta_mul_U L
  have hCap:2+gap L/exp L ≤ 2001/1000:=by rw [gap_ratio];exact two_add_delta_le_cap hL
  have hmin:∀rho∈S,min (gap L/exp L) ((2+gap L/exp L)/rho.im) ≤ 
      (2001/1000:ℝ)/max (U L) rho.im:=by
    intro rho hr
    exact E1FrozenN.Interval.min_le_clipped_reciprocal hU0 (hS rho hr).2.1.1 hδU hCap
  have hm:E1FrozenN.Interval.positiveZeroBudget (exp L) (gap L) Tstar ≤ 
      2*∑rho∈S,(IEANTN.zetaOrder rho:ℝ)*(exp L)^rho.re*((2001/1000:ℝ)/max (U L) rho.im):=by
    unfold E1FrozenN.Interval.positiveZeroBudget
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro rho hr
    have hw:=CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self (hS rho hr)
    exact mul_le_mul_of_nonneg_left (hmin rho hr) (mul_nonneg hw (by positivity))
  have he:2*∑rho∈S,(IEANTN.zetaOrder rho:ℝ)*(exp L)^rho.re*((2001/1000:ℝ)/max (U L) rho.im)=
      gap L*(2*U L*(∑rho∈S,((IEANTN.zetaOrder rho:ℝ)/max (U L) rho.im)*exp (-(1-rho.re)*L))):=by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hr
    rw [Real.rpow_def_of_pos (exp_pos L),log_exp]
    have hexp:gap L*U L*exp (-(1-rho.re)*L)=(2001/1000:ℝ)*exp (L*rho.re):=by
      rw [gap_mul_U]
      calc
        _ = (2001/1000:ℝ)*(exp L*exp (-(1-rho.re)*L)) := by ring
        _ = _ := by rw [←exp_add];congr 1;congr 1;ring
    calc
      _ = 2*((IEANTN.zetaOrder rho:ℝ)/max (U L) rho.im)*((2001/1000:ℝ)*exp (L*rho.re)) := by ring
      _ = _ := by rw [←hexp];ring
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hb (gap_pos L).le)

/-- All source assumptions remain explicit; the desired density or interval
bound is not a hypothesis. The actual common CHJ height feeds the actual CDF. -/
theorem psi_increment_error_profile
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330 ≤ L) :
    |Chebyshev.psi (exp L+gap L)-Chebyshev.psi (exp L)-gap L| ≤ 
      (low L+high L+49/100000)*gap L := by
  have hdom:=truncation_domain hL
  obtain ⟨Tstar,hTlo,hThi,herr⟩:=E1FrozenN.Interval.chjii_to_positive_budget hsource hQRH
    (exp_le_exp.mpr (by linarith : (40:ℝ) ≤ L)) (gap_pos L).le hdom.1 hdom.2
  have hs:Tstar ≤ V L:=by simpa only [V] using hThi
  have hb:=positive_budget_le_profile hrvm h8 hRH hQRH hL hs
  have ht:=truncation_error_bound hL
  rw [log_exp] at herr
  nlinarith

theorem psi_increment_relative_profile
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330 ≤ L) :
    |Chebyshev.psi (exp L+gap L)-Chebyshev.psi (exp L)-gap L|/gap L ≤ low L+high L+49/100000 :=
  (div_le_iff₀ (gap_pos L)).mpr (psi_increment_error_profile hsource h8 hRH hrvm hQRH hL)

theorem theta_increment_lower_profile
    (hsource:E1FrozenN.Interval.CHJII_Theorem1_3_Row40)
    (h8:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {L:ℝ} (hL:330 ≤ L) :
    (1-(low L+high L+491/1000000))*gap L ≤ 
      Chebyshev.theta (exp L+gap L)-Chebyshev.theta (exp L) := by
  have hp:=(abs_le.mp (psi_increment_error_profile hsource h8 hRH hrvm hQRH hL)).1
  have hpp:=prime_power_error_bound hL
  have hx:=Chebyshev.theta_le_psi (exp L)
  nlinarith

end E1NPlus
#print axioms E1NPlus.psi_increment_error_profile
