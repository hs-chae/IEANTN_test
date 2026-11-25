/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Rays
import G28FiniteNorm
import G28FiniteWing
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RH080.Gaussian28
open RH080.Gaussian40

theorem exp_neg_135_upper : Real.exp (-135) ≤ (3/100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  have he := exp_neg_upper_reduction (135 : ℚ) (68337078671325660483665556868919836766070752902304899989745391774044875115065/115792089237316195423570985008687907853269984665640564039457584007913129639936 : ℚ)
    (3/100000000000000000000000000000000000000000000000000000000000 : ℚ)
    (by norm_num) 256 24 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num)
  simpa only [Rat.cast_ofNat, Rat.cast_div] using he

theorem norm_tail_integral_upper :
    (∫ u in Ioi (12 : ℝ), radialGaussian true normSource u) ≤ (1/10000000000000 : ℝ) := by
  have ht := radialGaussian_infinite_tail true normSource (by decide)
  have hB : 0 ≤ (tailBudget 0 normSource : ℝ) := by exact_mod_cast tailBudget_nonneg normSource 0
  calc
    _ ≤ (tailBudget 0 normSource : ℝ)*Real.exp (-135)*8 := ht
    _ ≤ (tailBudget 0 normSource : ℝ)*(3/100000000000000000000000000000000000000000000000000000000000)*8 := by gcongr; exact exp_neg_135_upper
    _ ≤ (1/10000000000000 : ℝ) := by norm_num [tailBudget, normSource]

theorem wing_tail_integral_upper :
    (∫ u in Ioi (12 : ℝ), radialGaussian false wingSource u) ≤ (1/10000000000000 : ℝ) := by
  have ht := radialGaussian_infinite_tail false wingSource (by decide)
  have hB : 0 ≤ (tailBudget 0 wingSource : ℝ) := by exact_mod_cast tailBudget_nonneg wingSource 0
  calc
    _ ≤ (tailBudget 0 wingSource : ℝ)*Real.exp (-135)*8 := ht
    _ ≤ (tailBudget 0 wingSource : ℝ)*(3/100000000000000000000000000000000000000000000000000000000000)*8 := by gcongr; exact exp_neg_135_upper
    _ ≤ (1/10000000000000 : ℝ) := by norm_num [tailBudget, wingSource]

theorem norm_ray_integral_upper :
    (∫ u in Ioi (0 : ℝ), radialGaussian true normSource u) ≤ (6632665210921/10000000000000 : ℝ) := by
  rw [radialGaussian_ray_split true normSource (by decide) 0 (by norm_num)]
  have hf : (∫ u in (0 : ℝ)..12, radialGaussian true normSource u) ≤ (663266521092/1000000000000 : ℝ) := by
    have hn := norm_finite_integral
    norm_num [radialGaussian] at hn ⊢
    exact hn
  linarith [norm_tail_integral_upper]

theorem wing_ray_integral_upper :
    (∫ u in Ioi (1772453850905/1000000000000 : ℝ), radialGaussian false wingSource u) ≤ (277723422241/10000000000000 : ℝ) := by
  rw [radialGaussian_ray_split false wingSource (by decide) (1772453850905/1000000000000) (by norm_num)]
  have hf : (∫ u in (1772453850905/1000000000000 : ℝ)..12, radialGaussian false wingSource u) ≤ (27772342224/1000000000000 : ℝ) := by
    have hw := wing_finite_integral
    norm_num [radialGaussian] at hw ⊢
    exact hw
  linarith [wing_tail_integral_upper]

/-- Rational scale bound used for both genuine G40 integrals. -/
theorem wing_start_le_sqrt_pi :
    (1772453850905/1000000000000 : ℝ) ≤ Real.sqrt Real.pi := by
  have hs := Real.sqrt_nonneg Real.pi
  have hsq := Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.pi_gt_d20]

theorem two_div_sqrt_pi_upper :
    (2 : ℝ)/Real.sqrt Real.pi ≤ 1128379167096/1000000000000 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  apply (div_le_iff₀ hs).2
  have hl := wing_start_le_sqrt_pi
  nlinarith

#print axioms norm_ray_integral_upper
#print axioms wing_ray_integral_upper
#print axioms two_div_sqrt_pi_upper
end RH080.Gaussian28
