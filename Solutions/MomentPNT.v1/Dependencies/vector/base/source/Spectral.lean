/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.CH2.v7.Conclusions
import ZeroCount
import Section9

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Counting bound used by the all-strip spectral estimate. -/
theorem zetaN_le_log (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small) {t : ℝ} (ht : 14 ≤ t) :
    ZeroCount.v1.zetaNClosed t ≤ t * Real.log t / (2 * Real.pi) := by
  have ht0 : 0 < t := by linarith
  have hn := CH2Section7Z.zetaN_le_brut hrvm hsmall (by linarith : 12 ≤ t)
  have hl : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
    Real.log_le_log (by positivity) (div_le_self ht0.le (by linarith [Real.pi_gt_three]))
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ t / (2 * Real.pi) by positivity)
  calc ZeroCount.v1.zetaNClosed t ≤ t / (2 * Real.pi) * Real.log t := hn.trans hm
    _ = t * Real.log t / (2 * Real.pi) := by ring

/-- The complete CH2 spectral estimate for zeros anywhere in the critical strip. -/
theorem all_strip_spectral_bound (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t ξ : ℝ} (ht : 1000 ≤ t) (hξ : |ξ| ≤ 1)
    (hfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ ‖CH2Section6.omegaPlus t 0 ρ + ξ * I * CH2Section6.thetaTS t 1 ρ‖)
      ≤ spectralBound t * (t / (2 * Real.pi)) := by
  classical
  have ht0 : 0 < t := by linarith
  have hp := Real.pi_pos
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  have hmono : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
      (fun ρ ↦ ‖CH2Section6.omegaPlus t 0 ρ + ξ * I * CH2Section6.thetaTS t 1 ρ‖)
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ t / Real.pi * (1 / ρ.im) + 2) := by
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
    exact mul_le_mul_of_nonneg_right hw
      (CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm)
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
  rw [he] at hmono
  have hI := mul_le_mul_of_nonneg_left (sum_inv_ordinates_le hrvm hsmall hlow
    (by linarith : 14 ≤ t)) (show 0 ≤ t / Real.pi by positivity)
  have hN := mul_le_mul_of_nonneg_left (zetaN_le_log hrvm hsmall
    (by linarith : 14 ≤ t)) (by norm_num : (0 : ℝ) ≤ 2)
  have heq : t / Real.pi * (Real.log t ^ 2 / (4 * Real.pi) + Real.log t / (2 * Real.pi))
      + 2 * (t * Real.log t / (2 * Real.pi)) = spectralBound t * (t / (2 * Real.pi)) := by
    unfold spectralBound
    ring
  linarith

end CH2QRH
