/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineIntegrals

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem collect_cell_moments (a : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1),
      ((6*(j:ℝ)^2+4*j+1)*a j + (6*(j:ℝ)^2+8*j+3)*a (j+1))) =
    a 0 + (∑ j ∈ Finset.Ico 1 (N+1), (12*(j:ℝ)^2+2)*a j) +
      (6*(N:ℝ)^2+8*N+3)*a (N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ N+1)]
    push_cast
    ring

def nodalHatMu2 (nodes : List ℚ) (m : ℕ) : ℝ :=
  (|node nodes 0|/6 + 2*(∑ j ∈ Finset.Ico 1 (nodes.length-1),
    |node nodes j| *((j:ℝ)^2+1/6))) / (m:ℝ)^3

theorem nodalMu2Upper_eq_nodalHatMu2 (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    nodalMu2Upper nodes m = nodalHatMu2 nodes m := by
  have hN : nodes.length-1 = (nodes.length-2)+1 := by omega
  have hc := collect_cell_moments (fun j => |node nodes j|) (nodes.length-2)
  rw [← hN, hlast, abs_zero, mul_zero, add_zero] at hc
  unfold nodalMu2Upper nodalHatMu2
  rw [hc]
  have hs : (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      (12*(j:ℝ)^2+2)*|node nodes j|) =
      12 * (∑ j ∈ Finset.Ico 1 (nodes.length-1),
        |node nodes j| *((j:ℝ)^2+1/6)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  <;> ring

theorem integrable_sq_mul_absoluteSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    Integrable (fun v : ℝ => v^2*absoluteSpectrum nodes m v) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hi0 := (integrable_sq_mul_scaled_shifted_hat m 0 hm0).const_mul |node nodes 0|
  have hi (j : ℕ) : Integrable (fun v : ℝ => |node nodes j| *
      (v^2*hat ((m:ℝ)*v-j) + v^2*hat ((m:ℝ)*v+j))) := by
    exact ((integrable_sq_mul_scaled_shifted_hat m j hm0).add
      (by simpa [sub_neg_eq_add] using integrable_sq_mul_scaled_shifted_hat m (-(j:ℝ)) hm0)).const_mul _
  have hsum := hi0.add (integrable_finsetSum (Finset.Ico 1 (nodes.length-1)) (fun j hj => hi j))
  apply hsum.congr
  filter_upwards with v
  simp only [absoluteSpectrum, Pi.add_apply, sub_zero]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

theorem integral_sq_mul_absoluteSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    (∫ v : ℝ, v^2*absoluteSpectrum nodes m v) = nodalHatMu2 nodes m := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hi0 : Integrable (fun v : ℝ => v^2*hat ((m:ℝ)*v)) := by
    simpa using integrable_sq_mul_scaled_shifted_hat m 0 hm'.ne'
  have hip (j : ℕ) : Integrable (fun v : ℝ => v^2*hat ((m:ℝ)*v+j)) := by
    simpa [sub_neg_eq_add] using integrable_sq_mul_scaled_shifted_hat m (-(j:ℝ)) hm'.ne'
  have hi (j : ℕ) : Integrable (fun v : ℝ => |node nodes j| *
      (v^2*hat ((m:ℝ)*v-j) + v^2*hat ((m:ℝ)*v+j))) :=
    ((integrable_sq_mul_scaled_shifted_hat m j hm'.ne').add (hip j)).const_mul _
  have heq : (fun v : ℝ => v^2*absoluteSpectrum nodes m v) = (fun v : ℝ =>
      |node nodes 0| *(v^2*hat ((m:ℝ)*v)) + ∑ j ∈ Finset.Ico 1 (nodes.length-1),
        |node nodes j| *(v^2*hat ((m:ℝ)*v-j) + v^2*hat ((m:ℝ)*v+j))) := by
    funext v
    simp only [absoluteSpectrum, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  have hpair (j : ℕ) : (∫ v : ℝ, |node nodes j| *
      (v^2*hat ((m:ℝ)*v-j) + v^2*hat ((m:ℝ)*v+j))) =
      2*|node nodes j| *((j:ℝ)^2+1/6)/(m:ℝ)^3 := by
    rw [integral_const_mul, integral_add (integrable_sq_mul_scaled_shifted_hat m j hm'.ne') (hip j),
      integral_sq_mul_scaled_shifted_hat m j hm',
      show (∫ v : ℝ, v^2*hat ((m:ℝ)*v+j)) = ((j:ℝ)^2+1/6)/(m:ℝ)^3 by
        simpa [sub_neg_eq_add] using integral_sq_mul_scaled_shifted_hat m (-(j:ℝ)) hm']
    ring
  rw [heq, integral_add (hi0.const_mul _) (integrable_finsetSum _ (fun j hj => hi j)),
    integral_const_mul, integral_finsetSum _ (fun j hj => hi j)]
  simp_rw [hpair]
  rw [show (∫ v : ℝ, v^2*hat ((m:ℝ)*v)) = (1/6)/(m:ℝ)^3 by
    simpa using integral_sq_mul_scaled_shifted_hat m 0 hm']
  unfold nodalHatMu2
  have hs : (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      2*|node nodes j| *((j:ℝ)^2+1/6)/(m:ℝ)^3) =
      2*(∑ j ∈ Finset.Ico 1 (nodes.length-1),
        |node nodes j| *((j:ℝ)^2+1/6))/(m:ℝ)^3 := by
    rw [← Finset.sum_div, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring

theorem integrable_sq_abs_affineSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    Integrable (fun v : ℝ => v^2*|affineSpectrum nodes m v|) := by
  apply (integrable_sq_mul_absoluteSpectrum nodes m hm).mono'
  · exact ((continuous_id.pow 2).mul (continuous_affineSpectrum nodes m).abs).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg v) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (abs_affineSpectrum_le_absoluteSpectrum nodes m v) (sq_nonneg v)

theorem integral_sq_abs_affineSpectrum_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    (∫ v : ℝ, v^2*|affineSpectrum nodes m v|) ≤ nodalMu2Upper nodes m := by
  rw [nodalMu2Upper_eq_nodalHatMu2 nodes m hlen hm hlast,
    ← integral_sq_mul_absoluteSpectrum nodes m hm]
  exact integral_mono (integrable_sq_abs_affineSpectrum nodes m hm)
    (integrable_sq_mul_absoluteSpectrum nodes m hm)
    (fun v => mul_le_mul_of_nonneg_left (abs_affineSpectrum_le_absoluteSpectrum nodes m v) (sq_nonneg v))

end RH080Next.Explicit
