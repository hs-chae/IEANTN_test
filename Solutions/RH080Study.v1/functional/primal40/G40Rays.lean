/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Tail
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian40

noncomputable def radialGaussian (absMode : Bool) (cs : List ℚ) (u : ℝ) : ℝ :=
  positivePartOrAbs absMode (coeffEval cs u)*Real.exp (-(u^2))

theorem positivePartOrAbs_nonneg (absMode : Bool) (x : ℝ) :
    0 ≤ positivePartOrAbs absMode x := by
  cases absMode <;> simp [positivePartOrAbs, abs_nonneg]

theorem positivePartOrAbs_le_abs (absMode : Bool) (x : ℝ) :
    positivePartOrAbs absMode x ≤ |x| := by
  cases absMode
  · exact max_le (abs_nonneg _) (le_abs_self _)
  · exact le_rfl

theorem continuous_radialGaussian (absMode : Bool) (cs : List ℚ) :
    Continuous (radialGaussian absMode cs) := by
  exact (continuous_positivePartOrAbs absMode cs).mul
    (Real.continuous_exp.comp (continuous_id.pow 2).neg)

theorem radialGaussian_nonneg (absMode : Bool) (cs : List ℚ) (u : ℝ) :
    0 ≤ radialGaussian absMode cs u :=
  mul_nonneg (positivePartOrAbs_nonneg _ _) (Real.exp_nonneg _)

/-- Integrability is proved from the actual analytic Gaussian tail majorant. -/
theorem integrableOn_radialGaussian_tail (absMode : Bool) (cs : List ℚ)
    (hn : cs.length ≤ 81) : IntegrableOn (radialGaussian absMode cs) (Ioi (12 : ℝ)) := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(x^2)/16)) := by
    have hg := integrable_exp_neg_mul_sq (b := (1/16 : ℝ)) (by norm_num)
    convert hg using 1 <;> funext x <;> congr 1 <;> ring
  have hg := (hgauss.const_mul ((tailBudget 0 cs : ℝ)*Real.exp (-135))).integrableOn
    (s := Ioi (12 : ℝ))
  apply Integrable.mono' hg
  · exact (continuous_radialGaussian absMode cs).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (radialGaussian_nonneg _ _ _)]
    apply le_trans (mul_le_mul_of_nonneg_right (positivePartOrAbs_le_abs absMode _)
      (Real.exp_nonneg _))
    simpa only [pow_zero, one_mul, zero_add] using
      coeff_gaussian_tail_point cs 0 (by simpa using hn) x hx.le

theorem radialGaussian_infinite_tail (absMode : Bool) (cs : List ℚ) (hn : cs.length ≤ 81) :
    (∫ u in Ioi (12 : ℝ), radialGaussian absMode cs u) ≤
      (tailBudget 0 cs : ℝ)*Real.exp (-135)*8 := by
  have hnorm := integrableOn_radialGaussian_tail true cs hn
  have hbound := integral_mono_of_nonneg
    (μ := volume.restrict (Ioi (12 : ℝ)))
    (f := radialGaussian absMode cs) (g := radialGaussian true cs)
    (ae_of_all _ (radialGaussian_nonneg absMode cs)) hnorm
    (ae_of_all _ (fun x => mul_le_mul_of_nonneg_right (positivePartOrAbs_le_abs absMode _)
      (Real.exp_nonneg _)))
  exact hbound.trans (coeff_gaussian_infinite_tail cs hn)

theorem integrableOn_radialGaussian_ray (absMode : Bool) (cs : List ℚ)
    (hn : cs.length ≤ 81) (a : ℝ) (ha : a ≤ 12) :
    IntegrableOn (radialGaussian absMode cs) (Ioi a) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha, integrableOn_union]
  exact ⟨(continuous_radialGaussian absMode cs).integrableOn_Icc.mono_set Ioc_subset_Icc_self,
    integrableOn_radialGaussian_tail absMode cs hn⟩

/-- Complete half-line assembly, with the infinite tail genuinely added. -/
theorem radialGaussian_ray_split (absMode : Bool) (cs : List ℚ)
    (hn : cs.length ≤ 81) (a : ℝ) (ha : a ≤ 12) :
    (∫ u in Ioi a, radialGaussian absMode cs u) =
      (∫ u in a..12, radialGaussian absMode cs u)+
      (∫ u in Ioi (12 : ℝ), radialGaussian absMode cs u) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha]
  rw [setIntegral_union (by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (not_lt_of_ge hx.2) hx') measurableSet_Ioi
    ((continuous_radialGaussian absMode cs).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrableOn_radialGaussian_tail absMode cs hn)]
  rw [intervalIntegral.integral_of_le ha]

#print axioms integrableOn_radialGaussian_ray
#print axioms radialGaussian_ray_split
end RH080.Gaussian40
