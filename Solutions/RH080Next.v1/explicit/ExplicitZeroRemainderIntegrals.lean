/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDerivativeIntegrals

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem abs_log_le_logplus (u r : ℝ) (hr : 0 < r) (hu : r < u) :
    |log u| ≤ max 0 (log u)+|log r| := by
  have hl : log r ≤ log u := Real.log_le_log hr hu.le
  rcases le_total 0 (log u) with h|h
  · rw [abs_of_nonneg h,max_eq_right h]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [abs_of_nonpos h,max_eq_left h,zero_add]
    linarith [neg_le_abs (log r)]

/-- The exact weighted derivative integral in the CMS zero-count error is
controlled by the central and tail envelopes. The cut is any positive real,
so no numerical grid or sampled truncation-height argument is involved. -/
theorem zero_remainder_integral_le (g : ℝ → ℝ) (hcont : Continuous g)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcentral : ∀ u ∈ Icc (0:ℝ) 1, |g u| ≤ B)
    (htail : ∀ u : ℝ, 1 < u → |g u| ≤ C/u^2)
    (Δ r : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => ((3/20:ℝ)*log (u/Δ)+3)*|g u|) (Ioi r) ∧
    (∫ u in Ioi r, ((3/20:ℝ)*log (u/Δ)+3)*|g u|) ≤
      (3/20:ℝ)*C+((3/20:ℝ)*log (1/Δ)+3)*(B+C) := by
  obtain ⟨hgi,hgm,hli,hlm⟩ := derivative_halfline_envelopes g hcont B C hB hC hcentral htail
  let L : ℝ := (3/20:ℝ)*log (1/Δ)+3
  let A : ℝ := (3/20:ℝ)*|log r|+(3/20:ℝ)*|log Δ|+3
  have hL : 0 ≤ L := by
    have hlog : 0 ≤ log (1/Δ) := log_nonneg ((one_le_div hΔ).mpr hΔ1)
    dsimp [L]
    linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsub : Ioi r ⊆ Ioi (0:ℝ) := fun u hu => hr.trans hu
  have hbound0 : IntegrableOn (fun u : ℝ => (3/20:ℝ)*(max 0 (log u)*|g u|)+A*|g u|) (Ioi (0:ℝ)) :=
    (hli.const_mul (3/20)).add (hgi.const_mul A)
  have hboundi := hbound0.mono_set hsub
  have hei : IntegrableOn (fun u : ℝ => ((3/20:ℝ)*log (u/Δ)+3)*|g u|) (Ioi r) := by
    apply hboundi.mono'
    · exact ((Real.measurable_log.comp (measurable_id.div_const Δ)).const_mul (3/20) |>.add_const 3 |>.mul hcont.abs.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 := hr.trans hu
      have hl := abs_log_le_logplus u r hr hu
      have hld : |log (u/Δ)| ≤ max 0 (log u)+|log r|+|log Δ| := by
        rw [log_div hu0.ne' hΔ.ne']
        exact (abs_sub _ _).trans (by linarith)
      have hpre : |(3/20:ℝ)*log (u/Δ)+3| ≤
          (3/20:ℝ)*max 0 (log u)+A := by
        have h := abs_add_le ((3/20:ℝ)*log (u/Δ)) 3
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/20)] at h
        norm_num at h
        dsimp [A]
        linarith
      rw [Real.norm_eq_abs,abs_mul,abs_abs]
      calc
        |(3/20:ℝ)*log (u/Δ)+3| *|g u| ≤ ((3/20:ℝ)*max 0 (log u)+A)*|g u| :=
          mul_le_mul_of_nonneg_right hpre (abs_nonneg (g u))
        _ = (3/20:ℝ)*(max 0 (log u)*|g u|)+A*|g u| := by ring
  let E : ℝ → ℝ := fun u => (3/20:ℝ)*(max 0 (log u)*|g u|)+L*|g u|
  have hEi : IntegrableOn E (Ioi (0:ℝ)) := (hli.const_mul (3/20)).add (hgi.const_mul L)
  have hpoint : ∀ u ∈ Ioi r, ((3/20:ℝ)*log (u/Δ)+3)*|g u| ≤ E u := by
    intro u hu
    have hu0 := hr.trans hu
    have heq : log (u/Δ) = log u+log (1/Δ) := by
      rw [log_div hu0.ne' hΔ.ne',log_div one_ne_zero hΔ.ne',log_one]
      ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right (le_max_right 0 (log u)) (abs_nonneg (g u))
    dsimp [E,L]
    nlinarith
  have he := setIntegral_mono_on hei (hEi.mono_set hsub) measurableSet_Ioi hpoint
  have hmon : (∫ u in Ioi r, E u) ≤ ∫ u in Ioi (0:ℝ), E u := by
    apply setIntegral_mono_set hEi
    · filter_upwards with u
      dsimp [E]
      positivity
    · exact ae_of_all _ (fun u hu => hsub hu)
  have hEbound : (∫ u in Ioi (0:ℝ), E u) ≤ (3/20:ℝ)*C+L*(B+C) := by
    dsimp [E]
    rw [integral_add (hli.const_mul (3/20)) (hgi.const_mul L),integral_const_mul,integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hlm (by norm_num)) (mul_le_mul_of_nonneg_left hgm hL)
  exact ⟨hei,he.trans (hmon.trans hEbound)⟩

#print axioms zero_remainder_integral_le
end RH080Next.Explicit
