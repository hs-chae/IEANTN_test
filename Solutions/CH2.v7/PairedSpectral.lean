/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ZeroSymmetry

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Convexity in the zero's real part, proved by the equal-product identity. -/
theorem paired_power_bound {x β b : ℝ} (hx : 1 ≤ x) (hb : b ≤ β) (hb' : 1 - b ≤ β) :
    x ^ b + x ^ (1 - b) ≤ x ^ β + x ^ (1 - β) := by
  have hx0 : 0 < x := by linarith
  have h1 := Real.rpow_le_rpow_of_exponent_le hx hb
  have h2 := Real.rpow_le_rpow_of_exponent_le hx hb'
  have he1 : x ^ b * x ^ (1 - b) = x := by
    rw [← Real.rpow_add hx0]
    ring_nf
    exact Real.rpow_one x
  have he2 : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0]
    ring_nf
    exact Real.rpow_one x
  have hp := Real.rpow_pos_of_pos hx0 β
  have hm := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
  nlinarith

/-- Pair an ordinate-dependent nonnegative weight without changing multiplicities. -/
theorem zsum_paired_weight_le {β t x : ℝ} (hqrh : IEANTN.ZetaZeroFreeHalfPlane β)
    (hx : 1 ≤ x) (f : ℝ → ℝ) (hf : ∀ u ∈ Set.Ioc 0 t, 0 ≤ f u) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ.im * x ^ ρ.re)
      ≤ ((x ^ β + x ^ (1 - β)) / 2) *
        IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ.im) := by
  classical
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  have hsym := zsum_zeroReflect (t := t) (fun ρ ↦ f ρ.im * x ^ ρ.re)
  simp only [zeroReflect, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub,
    neg_neg, Complex.sub_re, Complex.one_re, Complex.conj_re] at hsym
  have hpair : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ.im * x ^ ρ.re) +
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ.im * x ^ (1 - ρ.re)) ≤
      (x ^ β + x ^ (1 - β)) *
        IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ.im) := by
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
      CH2Section7Z.zetaZeroesSum_eq_sum hfin, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hm := (Set.Finite.mem_toFinset hfin).mp hρ
    have hr := zeroReflect_mem hm
    have hb := re_le_boundary hqrh hm.2.2 hm.2.1.1
    have hb' : 1 - ρ.re ≤ β := by
      simpa [zeroReflect] using re_le_boundary hqrh hr.2.2 hr.2.1.1
    have hp := mul_le_mul_of_nonneg_left (paired_power_bound hx hb hb')
      (mul_nonneg (hf ρ.im hm.2.1)
        (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm))
    nlinarith
  rw [hsym] at hpair
  nlinarith

/-- The reciprocal-ordinate majorant of the CH2 spectral weight. -/
theorem ordinate_majorant_sum_le (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate) {t : ℝ} (ht : 1000 ≤ t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) ≤ spectralBound t * (t / (2 * Real.pi)) := by
  classical
  have hp := Real.pi_pos
  have ht0 : 0 < t := by linarith
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  have he : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2)
      = t / Real.pi * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ 1 / ρ.im)
        + 2 * ZeroCount.v1.zetaNClosed t := by
    change _ = _ + 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun _ ↦ 1)
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
      CH2Section7Z.zetaZeroesSum_eq_sum hfin, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hI := mul_le_mul_of_nonneg_left (sum_inv_ordinates_le hrvm hsmall hlow
    (by linarith : 14 ≤ t)) (show 0 ≤ t / Real.pi by positivity)
  have hN := mul_le_mul_of_nonneg_left (zetaN_le_log hrvm hsmall
    (by linarith : 14 ≤ t)) (by norm_num : (0 : ℝ) ≤ 2)
  have heq : t / Real.pi * (Real.log t ^ 2 / (4 * Real.pi) + Real.log t / (2 * Real.pi))
      + 2 * (t * Real.log t / (2 * Real.pi)) = spectralBound t * (t / (2 * Real.pi)) := by
    unfold spectralBound
    ring
  rw [he]
  linarith


/-- The CH2 spectral sum with reflected-zero pairing, for the fixed-half-plane input. -/
theorem paired_spectral_bound (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t ξ x β : ℝ} (ht : 1000 ≤ t) (hξ : |ξ| ≤ 1) (hx : 1 ≤ x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane β)
    (hfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ ‖CH2Section6.omegaPlus t 0 ρ + ξ * I * CH2Section6.thetaTS t 1 ρ‖ * x ^ ρ.re)
      ≤ ((x ^ β + x ^ (1 - β)) / 2) * (spectralBound t * (t / (2 * Real.pi))) := by
  classical
  have ht0 : 0 < t := by linarith
  have hp := Real.pi_pos
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  have hmono : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ ‖CH2Section6.omegaPlus t 0 ρ + ξ * I * CH2Section6.thetaTS t 1 ρ‖ * x ^ ρ.re)
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ (t / Real.pi * (1 / ρ.im) + 2) * x ^ ρ.re) := by
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hm := (Set.Finite.mem_toFinset hfin).mp hρ
    have hr := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hm.2.2 hm.2.1.1.ne'
    have hi : ρ.im < t := lt_of_le_of_ne hm.2.1.2 (fun he ↦
      hfree ρ hm.2.2 (by rw [he, abs_of_pos ht0]))
    have hw := all_strip_weight_bound hcs ht hr.1 hr.2 hm.2.1.1 hi hξ
    rw [Complex.re_add_im] at hw
    have he : t / (Real.pi * ρ.im) = t / Real.pi * (1 / ρ.im) := by ring
    rw [he] at hw
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg (by linarith) _))
      (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm)
  exact hmono.trans ((zsum_paired_weight_le hqrh hx
    (fun u ↦ t / Real.pi * (1 / u) + 2) (by intro u hu; have : 0 < u := hu.1; positivity)).trans
    (mul_le_mul_of_nonneg_left (ordinate_majorant_sum_le hrvm hsmall hlow ht)
      (by positivity)))


end CH2QRH
