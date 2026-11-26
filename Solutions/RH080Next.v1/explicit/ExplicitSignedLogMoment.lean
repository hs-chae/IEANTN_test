/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology

namespace RH080Next.Explicit

private lemma hasDerivAt_log_tail (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => -(log u + 1) / u) (log x / x ^ 2) x := by
  have h := (((Real.hasDerivAt_log hx).add_const 1).neg).div (hasDerivAt_id x) hx
  have heq : log x / x ^ 2 = (-x⁻¹ * x - -(log x + 1) * 1) / x ^ 2 := by
    field_simp [hx]
    ring
  rw [heq]
  exact h

private lemma tendsto_log_tail :
    Tendsto (fun u : ℝ => -(log u + 1) / u) atTop (𝓝 0) := by
  have hl : Tendsto (fun u : ℝ => log u / u) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hi : Tendsto (fun u : ℝ => (1 : ℝ) / u) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0))
  simpa only [neg_div, add_div, neg_zero, add_zero] using (hl.add hi).neg

/-- This is the positive logarithmic tail in the explicit formula. The lower
endpoint is one, not the central cutoff tau. -/
theorem integrable_log_div_sq_tail :
    IntegrableOn (fun u : ℝ => log u / u ^ 2) (Ioi 1) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun u : ℝ => -(log u + 1) / u) (a := 1) (l := 0)
  · intro u hu
    exact hasDerivAt_log_tail u (ne_of_gt (lt_of_lt_of_le zero_lt_one hu))
  · intro u hu
    exact div_nonneg (Real.log_nonneg (le_of_lt hu)) (sq_nonneg u)
  · exact tendsto_log_tail

theorem integral_log_div_sq_tail :
    (∫ u in Ioi (1 : ℝ), log u / u ^ 2) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun u : ℝ => -(log u + 1) / u)
    (g' := fun u : ℝ => log u / u ^ 2) (l := 0)
    (a := 1) (fun u hu => hasDerivAt_log_tail u
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hu)))
    (fun u hu => div_nonneg (Real.log_nonneg (le_of_lt hu)) (sq_nonneg u))
    tendsto_log_tail
  simpa using h

/-- The middle region contributes a nonpositive amount without any sign
hypothesis on F itself. It is the logarithmic weight that is signed. -/
theorem signed_log_middle_pointwise (F : ℝ → ℝ) (u : ℝ)
    (hu0 : 0 < u) (hu1 : u ≤ 1) : |F u| * log u ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (Real.log_nonpos hu0.le hu1)

/-- The lower quadratic control on F also lower-bounds |F|, even if the
quadratic expression or F becomes negative. -/
theorem signed_log_center_pointwise (F : ℝ → ℝ) (f0 b u : ℝ)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hlower : f0 - b * u ^ 2 ≤ F u) :
    |F u| * log u ≤ (f0 - b * u ^ 2) * log u := by
  exact mul_le_mul_of_nonpos_right (hlower.trans (le_abs_self _))
    (Real.log_nonpos hu0.le hu1)

/-- The tail estimate requires u>1, where log is nonnegative. -/
theorem signed_log_tail_pointwise (F : ℝ → ℝ) (v u : ℝ)
    (hu : 1 < u) (hbound : |F u| ≤ v / u ^ 2) :
    |F u| * log u ≤ v * (log u / u ^ 2) := by
  have h := mul_le_mul_of_nonneg_right hbound (Real.log_nonneg hu.le)
  calc
    |F u| * log u ≤ (v / u ^ 2) * log u := h
    _ = v * (log u / u ^ 2) := by ring

private lemma continuous_sq_mul_log : Continuous (fun u : ℝ => u ^ 2 * log u) := by
  convert continuous_id.mul Real.continuous_mul_log using 1
  funext u
  simp only [Pi.mul_apply, id_eq]
  ring

private lemma continuous_cubic_log_primitive :
    Continuous (fun u : ℝ => u ^ 3 * log u / 3 - u ^ 3 / 9) := by
  have h := ((continuous_id.pow 2).mul Real.continuous_mul_log).div_const 3
  convert h.sub ((continuous_id.pow 3).div_const 9) using 1
  funext u
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  ring

private lemma hasDerivAt_cubic_log_primitive (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ 3 * log x / 3 - x ^ 3 / 9)
      (u ^ 2 * log u) u := by
  have h := ((((hasDerivAt_id u).pow 3).mul (Real.hasDerivAt_log hu)).div_const 3).sub
    (((hasDerivAt_id u).pow 3).div_const 9)
  apply h.congr_deriv
  dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  norm_num
  field_simp [hu]
  ring

theorem integral_sq_mul_log_from_zero (τ : ℝ) (hτ : 0 < τ) :
    (∫ u in (0 : ℝ)..τ, u ^ 2 * log u) = τ ^ 3 * log τ / 3 - τ ^ 3 / 9 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.le
    continuous_cubic_log_primitive.continuousOn
    (fun u hu => hasDerivAt_cubic_log_primitive u hu.1.ne')
    (continuous_sq_mul_log.intervalIntegrable 0 τ)
  simpa using h

theorem intervalIntegrable_center_log (f0 b τ : ℝ) :
    IntervalIntegrable (fun u : ℝ => (f0 - b * u ^ 2) * log u) volume 0 τ := by
  have hlog := intervalIntegral.intervalIntegrable_log' (a := 0) (b := τ)
  convert (hlog.const_mul f0).sub
    ((continuous_sq_mul_log.intervalIntegrable 0 τ).const_mul b) using 1
  funext u
  ring

/-- Exact central contribution, including its negative leading term. -/
theorem integral_center_log (f0 b τ : ℝ) (hτ : 0 < τ) :
    (∫ u in (0 : ℝ)..τ, (f0 - b * u ^ 2) * log u) =
      f0 * (τ * log τ - τ) - b * (τ ^ 3 * log τ / 3 - τ ^ 3 / 9) := by
  have hlog := intervalIntegral.intervalIntegrable_log' (a := 0) (b := τ)
  have heq : (fun u : ℝ => (f0 - b * u ^ 2) * log u) =
      (fun u : ℝ => f0 * log u - b * (u ^ 2 * log u)) := by
    funext u
    ring
  rw [heq, intervalIntegral.integral_sub (hlog.const_mul f0)
    ((continuous_sq_mul_log.intervalIntegrable 0 τ).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sq_mul_log_from_zero τ hτ]
  simp only [integral_log, zero_mul, sub_zero, add_zero]

theorem two_positive_log_moment_le (F : ℝ → ℝ) (f0 b v τ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hint : IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 0))
    (hlower : ∀ u ∈ Icc (0 : ℝ) τ, f0 - b * u ^ 2 ≤ F u)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ v / u ^ 2) :
    2 * (∫ u in Ioi (0 : ℝ), |F u| * log u) ≤
      2 * v - 2 * f0 * τ * (1 - log τ) +
        2 * b * τ ^ 3 * (1 / 9 - log τ / 3) := by
  let g : ℝ → ℝ := fun u => |F u| * log u
  have h01 : IntegrableOn g (Ioc 0 1) := hint.mono_set (by intro u hu; exact hu.1)
  have h1 : IntegrableOn g (Ioi 1) :=
    hint.mono_set (by
      intro u hu
      have h : (1 : ℝ) < u := hu
      exact lt_trans zero_lt_one h)
  have h0τ : IntervalIntegrable g volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mpr
      (hint.mono_set (by intro u hu; exact hu.1))
  have hτint : IntervalIntegrable g volume τ 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ1).mpr
      (hint.mono_set (by intro u hu; exact lt_trans hτ hu.1))
  have hc : (∫ u in (0 : ℝ)..τ, g u) ≤
      ∫ u in (0 : ℝ)..τ, (f0 - b * u ^ 2) * log u := by
    apply intervalIntegral.integral_mono_on hτ.le h0τ
      (intervalIntegrable_center_log f0 b τ)
    intro u hu
    by_cases hu0 : u = 0
    · simp [g, hu0]
    · exact signed_log_center_pointwise F f0 b u
        (lt_of_le_of_ne hu.1 (Ne.symm hu0)) (hu.2.trans hτ1) (hlower u hu)
  have hm := intervalIntegral.integral_mono_on hτ1 hτint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume τ 1)
    (fun u hu => signed_log_middle_pointwise F u (lt_of_lt_of_le hτ hu.1) hu.2)
  have ht := setIntegral_mono_on h1 (integrable_log_div_sq_tail.const_mul v)
    measurableSet_Ioi (fun u hu => signed_log_tail_pointwise F v u hu (htail u hu))
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ 1
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr (lt_of_not_ge hu)
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [disjoint_left]
    intro u hu hv
    have hv' : (1 : ℝ) < u := hv
    exact (not_lt_of_ge hu.2) hv'
  have hsplit := setIntegral_union hd measurableSet_Ioi h01 h1
  rw [hs, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  rw [← intervalIntegral.integral_add_adjacent_intervals h0τ hτint] at hsplit
  rw [integral_center_log f0 b τ hτ] at hc
  simp only [intervalIntegral.integral_zero] at hm
  rw [integral_const_mul, integral_log_div_sq_tail, mul_one] at ht
  dsimp [g] at hsplit hc hm ht
  nlinarith

/-- Whole-real signed logarithmic moment. Absolute Fourier amplitude is retained;
the negative contribution comes only from the logarithm near zero. -/
theorem signed_log_moment_le (F : ℝ → ℝ) (f0 b v τ : ℝ)
    (heven : Function.Even F) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hint : IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 0))
    (hlower : ∀ u ∈ Icc (0 : ℝ) τ, f0 - b * u ^ 2 ≤ F u)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ v / u ^ 2) :
    (∫ u : ℝ, |F u| * log |u|) ≤
      2 * v - 2 * f0 * τ * (1 - log τ) +
        2 * b * τ ^ 3 * (1 / 9 - log τ / 3) := by
  have heq : (fun u : ℝ => |F u| * log |u|) =
      (fun u : ℝ => |F (|u|)| * log |u|) := by
    funext u
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), heven u]
  rw [heq, integral_comp_abs (f := fun u : ℝ => |F u| * log u)]
  exact two_positive_log_moment_le F f0 b v τ hτ hτ1 hint hlower htail

/-- The exact 4*pi² moment coefficient before safe rational enlargement. -/
theorem signed_log_moment_fourier_bound (F : ℝ → ℝ) (f0 V1 μ2 τ : ℝ)
    (heven : Function.Even F) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hint : IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 0))
    (hlower : ∀ u ∈ Icc (0 : ℝ) τ, f0 - 2 * π ^ 2 * μ2 * u ^ 2 ≤ F u)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ V1 / (4 * π ^ 2 * u ^ 2)) :
    (∫ u : ℝ, |F u| * log |u|) ≤
      V1 / (2 * π ^ 2) - 2 * f0 * τ * (1 - log τ) +
        4 * π ^ 2 * μ2 * τ ^ 3 * (1 / 9 - log τ / 3) := by
  have h := signed_log_moment_le F f0 (2 * π ^ 2 * μ2) (V1 / (4 * π ^ 2)) τ
    heven hτ hτ1 hint hlower (by
      intro u hu
      convert htail u hu using 1 <;> field_simp <;> ring)
  convert h using 1 <;> field_simp <;> ring

/-- The safe rational coefficient40 used in both stored numerical evaluations.
Its only enlargement is 4*pi²<40; no numerical moment result is assumed. -/
theorem signed_log_moment_fourier_bound_40 (F : ℝ → ℝ) (f0 V1 μ2 τ : ℝ)
    (heven : Function.Even F) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hμ : 0 ≤ μ2)
    (hint : IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 0))
    (hlower : ∀ u ∈ Icc (0 : ℝ) τ, f0 - 2 * π ^ 2 * μ2 * u ^ 2 ≤ F u)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ V1 / (4 * π ^ 2 * u ^ 2)) :
    (∫ u : ℝ, |F u| * log |u|) ≤
      V1 / (2 * π ^ 2) - 2 * f0 * τ * (1 - log τ) +
        40 * μ2 * τ ^ 3 * (1 / 9 - log τ / 3) := by
  have h := signed_log_moment_fourier_bound F f0 V1 μ2 τ heven hτ hτ1 hint hlower htail
  have hp : 4 * π ^ 2 ≤ 40 := by
    have hmul := mul_pos (sub_pos.mpr Real.pi_lt_d2)
      (show 0 < (3.15 : ℝ) + π by linarith [Real.pi_pos])
    nlinarith
  have hz : 0 ≤ μ2 * τ ^ 3 * (1 / 9 - log τ / 3) :=
    mul_nonneg (mul_nonneg hμ (pow_nonneg hτ.le _))
      (by linarith [Real.log_nonpos hτ.le hτ1])
  have hm := mul_le_mul_of_nonneg_right hp hz
  nlinarith

/-- Continuity at finite points and quadratic decay suffice for the actual
positive-axis signed-log integral to exist. -/
theorem integrableOn_signed_log_of_continuous_tail (F : ℝ → ℝ)
    (hF : Continuous F) (v : ℝ)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ v / u ^ 2) :
    IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 0) := by
  have hi01 : IntervalIntegrable (fun u : ℝ => |F u| * log u) volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).mul_continuousOn
      hF.abs.continuousOn
    convert h using 1
    funext u
    ring
  have h01 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi01
  have h1 : IntegrableOn (fun u : ℝ => |F u| * log u) (Ioi 1) := by
    apply Integrable.mono' (integrable_log_div_sq_tail.const_mul v)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : (1 : ℝ) < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.log_nonneg hu'.le))]
      exact signed_log_tail_pointwise F v u hu' (htail u hu')
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext u
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hu : u ≤ 1
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr (lt_of_not_ge hu)
  simpa only [hs] using h01.union h1

theorem integrable_comp_abs_of_integrableOn_positive (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x : ℝ => f |x|) := by
  have hp : IntegrableOn (fun x : ℝ => f |x|) (Ioi 0) := by
    apply hf.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  have hn : IntegrableOn (fun x : ℝ => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

theorem integrable_signed_log_of_continuous_even_tail (F : ℝ → ℝ)
    (hF : Continuous F) (heven : Function.Even F) (v : ℝ)
    (htail : ∀ u : ℝ, 1 < u → |F u| ≤ v / u ^ 2) :
    Integrable (fun u : ℝ => |F u| * log |u|) := by
  have hi := integrable_comp_abs_of_integrableOn_positive
    (fun u : ℝ => |F u| * log u) (integrableOn_signed_log_of_continuous_tail F hF v htail)
  convert hi using 1
  funext u
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg (lt_of_not_ge hu), heven u]

end RH080Next.Explicit
