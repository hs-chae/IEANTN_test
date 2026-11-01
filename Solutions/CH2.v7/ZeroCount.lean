/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GeneralTitch
import ZeroWeights
import IEANTN.Nodes.LowZeroes.v1.Conclusions

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The existing first-ordinate computation excludes the whole closed low-height interval. -/
theorem no_low_zero (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : 0 < ρ.im) (hi : ρ.im ≤ 14) : False := by
  have hempty : IEANTN.zetaZeroesIn Set.univ (Set.Ioo 0 (14.134725 : ℝ)) = ∅ := by
    simpa [LowZeroes.v1.no_zeroes_below_first_ordinate, IEANTN.margin] using hlow
  have hm : ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioo 0 (14.134725 : ℝ)) :=
    ⟨trivial, ⟨him, by linarith⟩, hz⟩
  rw [hempty] at hm
  exact Set.notMem_empty ρ hm

/-- The reciprocal-ordinate sum from the existing CH2 counting and partial-summation proofs. -/
theorem sum_inv_ordinates_le (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t : ℝ} (ht : 14 ≤ t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ 1 / ρ.im)
      ≤ Real.log t ^ 2 / (4 * Real.pi) + Real.log t / (2 * Real.pi) := by
  classical
  have ht0 : 0 < t := by linarith
  have hp := Real.pi_pos
  have hempty : IEANTN.zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 14) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    exact no_low_zero hlow hρ.2.2 hρ.2.1.1 hρ.2.1.2
  have hzero : ∀ f : ℂ → ℝ,
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc (0 : ℝ) 14) f = 0 := by
    intro f
    simp [IEANTN.zetaZeroesSum, hempty]
  have hN14 : ZeroCount.v1.zetaNClosed 14 = 0 := by
    exact hzero (fun _ ↦ 1)
  have hcount : ∀ u ∈ Set.Icc (14 : ℝ) t,
      ZeroCount.v1.zetaNClosed u ≤ u * Real.log u / (2 * Real.pi) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hn := CH2Section7Z.zetaN_le_brut hrvm hsmall (by linarith [hu.1] : 12 ≤ u)
    have hl : Real.log (u / (2 * Real.pi)) ≤ Real.log u :=
      Real.log_le_log (by positivity) (div_le_self hu0.le (by linarith [Real.pi_gt_three]))
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ u / (2 * Real.pi) by positivity)
    calc ZeroCount.v1.zetaNClosed u ≤ u / (2 * Real.pi) * Real.log u := hn.trans hm
      _ = u * Real.log u / (2 * Real.pi) := by ring
  have hderiv : ∀ u ∈ Set.uIcc (14 : ℝ) t,
      HasDerivAt (fun v : ℝ ↦ 1 / v) (-1 / u ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    simpa only [neg_div, one_div] using hasDerivAt_inv hu0
  have hcont : ContinuousOn (fun u : ℝ ↦ -1 / u ^ 2) (Set.uIcc 14 t) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
    exact (by fun_prop (disch := assumption) : ContinuousAt (fun u : ℝ ↦ -1 / u ^ 2) u).continuousWithinAt
  obtain ⟨hid, hint⟩ := CH2Section81.lehman_identity (by norm_num : (0 : ℝ) < 14) ht hderiv hcont
  simp only [hN14, sub_zero] at hid hint
  have hfun : (fun u : ℝ ↦ -1 / u ^ 2 * ZeroCount.v1.zetaNClosed u)
      = -(fun u : ℝ ↦ ZeroCount.v1.zetaNClosed u / u ^ 2) := by
    funext u
    simp only [Pi.neg_apply]
    ring
  rw [hfun] at hid
  change IEANTN.zetaZeroesSum Set.univ (Set.Ioc 14 t) (fun ρ ↦ 1 / ρ.im)
    = 1 / t * ZeroCount.v1.zetaNClosed t
      - (∫ u in (14 : ℝ)..t, -(ZeroCount.v1.zetaNClosed u / u ^ 2)) at hid
  rw [intervalIntegral.integral_neg, sub_neg_eq_add] at hid
  rw [hfun] at hint
  have hNi : IntervalIntegrable (fun u : ℝ ↦ ZeroCount.v1.zetaNClosed u / u ^ 2)
      volume 14 t := by simpa only [neg_neg] using hint.neg
  have hGi : IntervalIntegrable (fun u : ℝ ↦ Real.log u / (2 * Real.pi * u)) volume 14 t := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hden : 2 * Real.pi * u ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu0
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun u : ℝ ↦ Real.log u / (2 * Real.pi * u)) u).continuousWithinAt
  have hI := intervalIntegral.integral_mono_on ht hNi hGi (fun u hu ↦ ?_)
  swap
  · have hu0 : 0 < u := by linarith [hu.1]
    rw [div_le_iff₀ (by positivity : 0 < u ^ 2)]
    have he : Real.log u / (2 * Real.pi * u) * u ^ 2 = u * Real.log u / (2 * Real.pi) := by
      field_simp
    rw [he]
    exact hcount u hu
  have hGd : ∀ u ∈ Set.uIcc (14 : ℝ) t,
      HasDerivAt (fun v : ℝ ↦ Real.log v ^ 2 / (4 * Real.pi))
        (Real.log u / (2 * Real.pi * u)) u := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    convert ((Real.hasDerivAt_log hu0).pow 2).div_const (4 * Real.pi) using 1 <;> first | rfl | (norm_num; field_simp; ring)
  have hGeq := intervalIntegral.integral_eq_sub_of_hasDerivAt hGd hGi
  rw [hGeq] at hI
  have hE : 1 / t * ZeroCount.v1.zetaNClosed t ≤ Real.log t / (2 * Real.pi) := by
    have hc := hcount t ⟨ht, le_rfl⟩
    rw [show 1 / t * ZeroCount.v1.zetaNClosed t = ZeroCount.v1.zetaNClosed t / t by ring,
      div_le_iff₀ ht0]
    calc ZeroCount.v1.zetaNClosed t ≤ t * Real.log t / (2 * Real.pi) := hc
      _ = Real.log t / (2 * Real.pi) * t := by ring
  rw [CH2Section7A.zsum_split (by norm_num : (0 : ℝ) ≤ 14) ht, hzero, zero_add, hid]
  have hl : 0 ≤ Real.log (14 : ℝ) ^ 2 / (4 * Real.pi) := by positivity
  linarith

end CH2QRH
