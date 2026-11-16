/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GeneralHorizontal
import DensitySpectral
import PairedEnvelope
import Section9Limit
import IEANTN.Vocabulary.ErrorTerms

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7
open CH2Section6 CH2Section81 CH2Section9


/-- The finite density layer remains explicit until its numerical envelope is certified. -/
noncomputable def densitySpectralBound (t x : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / 4) * CH2.v7.spectralBound t + Real.log x *
    (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * finiteDensityWeight σ t)

set_option maxHeartbeats 1000000 in
/-- CH2's finite explicit formula with the fixed-half-plane spectral input.
The hypotheses are existing CH2 source inputs and the zero-free half-plane itself. -/
theorem density_transfer_at_height (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    {T x : ℝ} (hT : 3 * (10 : ℝ) ^ (12 : ℕ) + 1 ≤ T) (hR : 16 ≤ Real.log T)
    (hx1 : 1000000 ≤ x) (hxlog : 1 ≤ Real.log x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      |Chebyshev.psi x / x -
        (Real.pi / t * (Real.cosh (Real.pi / t) / Real.sinh (Real.pi / t))
          - Real.log (2 * Real.pi) / x)|
      ≤ Real.pi / t + densitySpectralBound t x +
        2 * (horizontalCorrection T t x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
          1.8 / Real.log x ^ 3) / t ^ 2 +
        2 * Real.pi / (t * x) *
          ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) := by
  have hπ := Real.pi_pos
  have hx0 : 0 < x := by linarith
  obtain ⟨t, Δ, ht1, ht2, hΔ, hΔi, hTfree, hfar⟩ := exists_separated_height hrvm (by norm_num at hT; linarith : 2000 ≤ T)
  have ht0 : 0 < t := by linarith
  have ht1000 : 1000 ≤ t := by linarith
  have ht4 : 4 ≤ t := by linarith
  obtain ⟨hInt1, hInt2⟩ := horizontal_both_no_RH hH hrvm hsmall hv hfe ht1000 ht2 hR
    hxlog hx0 hΔ hΔi hfar
  obtain ⟨l, hsig, hlT, hlδ⟩ := exists_ladder (by linarith : 4 < t)
  have hRC := CH2Section6.hRC_of_rvm hsmall l hlδ
  have hTfree' : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T := by rw [hlT]; exact hTfree
  have hlam : CH2Section6.lamOf l.T 0 < 0 := CH2Section6.lamOf_neg l.hT (by norm_num)
  have hsig0 : 0 ≤ l.sigmaOf (CH2Section6.lamOf l.T 0) := by
    rw [CH2Section6.sigmaOf_lamOf l (by norm_num)]
  have htH : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t := by linarith
  set V := densitySpectralBound t x with hV
  have hZ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc l.δ l.T)
        (fun ρ ↦ ‖CH2Section6.omegaPlus l.T 0 ρ + ε * I * CH2Section6.thetaTS l.T 1 ρ‖ *
          x ^ ρ.re) ≤ (x * t / (2 * Real.pi)) * V := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [hlδ, hlT, zsum_Iic_Ioc_eq hsmall]
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
    have hmono : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ ‖CH2Section6.omegaPlus t 0 ρ + ε * I * CH2Section6.thetaTS t 1 ρ‖ * x ^ ρ.re) ≤
        IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
          (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ ρ.re) := by
      rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
      apply Finset.sum_le_sum
      intro ρ hρ
      have hm := (Set.Finite.mem_toFinset hfin).mp hρ
      have hr := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hm.2.2 hm.2.1.1.ne'
      have hi : ρ.im < t := lt_of_le_of_ne hm.2.1.2 (fun he ↦
        hTfree ρ hm.2.2 (by rw [he, abs_of_pos ht0]))
      have hw := all_strip_weight_bound hcs ht1000 hr.1 hr.2 hm.2.1.1 hi hε1
      rw [Complex.re_add_im] at hw
      have he : t / (Real.pi * ρ.im) = t / Real.pi * (1 / ρ.im) := by ring
      rw [he] at hw
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hx0.le _))
        (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm)
    have hs := density_spectral_majorant hFKS hRH hrvm hsmall hlow htH
      (by linarith : 1 ≤ x) hqrh
    have heq : (2 * Real.pi / (t * x)) * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ ρ.re) =
        (2 * Real.pi / t) * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
          (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ (ρ.re - 1)) := by
      rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      rw [Real.rpow_sub_one hx0.ne']
      ring
    rw [← heq] at hs
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ x * t / (2 * Real.pi) by positivity)
    have hc : (x * t / (2 * Real.pi)) * ((2 * Real.pi / (t * x)) *
        IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
          (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ ρ.re)) =
        IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
          (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ ρ.re) := by field_simp
    rw [hc] at hh
    exact hmono.trans hh
  set J := horizontalCorrection T t x with hJ
  set K : ℝ := Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 with hK
  have hE : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      CH2Section6.shiftError l (CH2Section6.lamOf l.T 0) ε x ≤ x / (Real.pi * t) * (J + K) := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    have hC := CH2Section6.norm_intC_le hfe hdig hk hneg h2v l hlδ hlam hε1 (by rw [hlT]; exact ht4)
      hsig0 hRC hx1
    rw [hlT] at hC ⊢
    rw [CH2Section6.shiftError, hlT]
    have hKx : (Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3) / t
        = x * K / t := by rw [hK]; field_simp; try ring
    rw [hKx] at hC
    have e : x / (Real.pi * t) * (J + K)
        = 1 / (2 * Real.pi) * (1 / t * (x * J + x * J) + 2 * (x * K / t)) := by
      field_simp
      try ring
    rw [e]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hI1 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
        ≤ x * J := hInt1
    have hI2 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ x * J := by
      refine le_trans (le_of_eq ?_) hInt2
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      congr 2
      try push_cast
      try ring
    have hle : 1 / t * ((∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
          + ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ 1 / t * (x * J + x * J) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hmain := CH2Section6.svm_abs_bound hfe hdig h24u h24l hsig hTfree' hRC
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)
    (by simp [riemannZeta_zero] : riemannZeta (0 : ℂ) ≠ 0)
    (x₀ := 2) (by norm_num) (by linarith) hZ hE
  rw [hlT, CH2Section9.Svm_zero, Complex.ofReal_zero, CH2Section9.logDeriv_zeta_zero] at hmain
  simp only [Complex.ofReal_re, sub_zero, zero_sub, mul_one, Real.rpow_one] at hmain
  rw [Real.rpow_neg_one] at hmain
  simp only [← div_eq_mul_inv] at hmain
  refine ⟨t, ⟨ht1, by linarith⟩, hmain.trans_eq ?_⟩
  dsimp only [V, J, K]
  field_simp
  <;> ring

end CH2QRH
