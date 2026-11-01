/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTailMoments
import DensitySpectral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The FKS majorant is convex in the real-part parameter, on the entire real line. -/
theorem fksDensityMajorant_convex {u : ℝ} (hu : 1 < u) :
    ConvexOn ℝ Set.univ (fun σ ↦ fksDensityMajorant σ u) := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  let A : ℝ → ℝ := fun σ ↦ 8 * (1 - σ) / 3 * Real.log u +
    (5 - 2 * σ) * Real.log (Real.log u)
  have he : ∀ σ, fksDensityMajorant σ u =
      9.795 * Real.exp (A σ) + 4.465 * Real.log u ^ (2 : ℕ) := by
    intro σ
    unfold fksDensityMajorant A
    rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hlu]
    rw [show Real.log u * (8 * (1 - σ) / 3) = 8 * (1 - σ) / 3 * Real.log u by ring,
      show Real.log (Real.log u) * (5 - 2 * σ) = (5 - 2 * σ) * Real.log (Real.log u) by ring,
      Real.exp_add]
    ring
  refine ⟨convex_univ, ?_⟩
  intro σ _ σ' _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [he, he, he]
  have hA : A (a * σ + b * σ') = a * A σ + b * A σ' := by
    dsimp [A]
    linear_combination -(8 / 3 * Real.log u + 5 * Real.log (Real.log u)) * hab
  rw [hA]
  have hh := convexOn_exp.2 (Set.mem_univ (A σ)) (Set.mem_univ (A σ')) ha hb hab
  simp only [smul_eq_mul] at hh
  have hconst : a * (4.465 * Real.log u ^ (2 : ℕ)) +
      b * (4.465 * Real.log u ^ (2 : ℕ)) = 4.465 * Real.log u ^ (2 : ℕ) := by
    rw [← add_mul, hab, one_mul]
  nlinarith

/-- Integrability in height, including every interpolated real part. -/
theorem fksDensityMajorant_height_integrable {σ H t : ℝ} (hH : 1 < H) (ht : H ≤ t) :
    IntervalIntegrable (fun u ↦ fksDensityMajorant σ u / u ^ 2) volume H t := by
  apply ContinuousOn.intervalIntegrable_of_Icc ht
  intro u hu
  have hu1 : 1 < u := hH.trans_le hu.1
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu1
  unfold fksDensityMajorant
  exact (((continuousAt_const.mul (Real.continuousAt_rpow_const u _ (Or.inl hu0.ne'))).mul
    ((Real.continuousAt_log hu0.ne').rpow_const (Or.inl hlu.ne'))).add
      (continuousAt_const.mul ((Real.continuousAt_log hu0.ne').pow 2))).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hu0.ne') |>.continuousWithinAt

/-- Convexity survives the finite height integral, with all scalar signs checked. -/
theorem finiteDensityWeight_convex {t : ℝ} (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    ConvexOn ℝ Set.univ (fun σ ↦ finiteDensityWeight σ t) := by
  have hH : (1 : ℝ) < 3 * (10 : ℝ) ^ (12 : ℕ) := by norm_num
  have ht1 : 1 < t := hH.trans_le ht
  have ht0 : 0 < t := by linarith
  refine ⟨convex_univ, ?_⟩
  intro σ _ σ' _ a b ha hb hab
  simp only [smul_eq_mul]
  have hpoint : ∀ u : ℝ, 1 < u → fksDensityMajorant (a * σ + b * σ') u ≤
      a * fksDensityMajorant σ u + b * fksDensityMajorant σ' u := by
    intro u hu
    exact (fksDensityMajorant_convex hu).2 trivial trivial ha hb hab
  have hI := fksDensityMajorant_height_integrable (σ := σ) hH ht
  have hJ := fksDensityMajorant_height_integrable (σ := σ') hH ht
  have hK := fksDensityMajorant_height_integrable (σ := a * σ + b * σ') hH ht
  have hi := intervalIntegral.integral_mono_on ht hK ((hI.const_mul a).add (hJ.const_mul b))
    (fun u hu ↦ by
      have hu0 : 0 < u := by linarith [hu.1, hH]
      have hh := div_le_div_of_nonneg_right (hpoint u (hH.trans_le hu.1)) (sq_nonneg u)
      convert hh using 1 <;> first | rfl | ring)
  rw [intervalIntegral.integral_add (hI.const_mul a) (hJ.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hf := hpoint t ht1
  have hc : 0 ≤ 4 * Real.pi / t := by positivity
  have hdiv := div_le_div_of_nonneg_right hf ht0.le
  have hmul := mul_le_mul_of_nonneg_left hf hc
  unfold finiteDensityWeight
  have hsum := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hdiv hi)
    (by norm_num : (0 : ℝ) ≤ 2)) hmul
  convert hsum using 1 <;> first | rfl | ring

end CH2QRH
