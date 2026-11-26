/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitHatIntegrals

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem integrable_hat : Integrable hat := by
  simpa using integrable_pow_mul_hat 0

theorem integrable_scaled_shifted_hat (m j : ℝ) (hm : m ≠ 0) :
    Integrable (fun v : ℝ => hat (m*v-j)) := by
  exact (integrable_hat.comp_sub_right j).comp_mul_left' hm

theorem integral_scaled_shifted_hat (m j : ℝ) (hm : 0 < m) :
    (∫ v : ℝ, hat (m*v-j)) = 1/m := by
  rw [Measure.integral_comp_mul_left (fun x : ℝ => hat (x-j)) m,
    integral_sub_right_eq_self, integral_hat]
  simp [abs_of_pos (inv_pos.mpr hm), one_div]

private theorem integrable_shifted_sq_hat (j : ℝ) :
    Integrable (fun x : ℝ => (x+j)^2 * hat x) := by
  have heq : (fun x : ℝ => (x+j)^2 * hat x) =
      (fun x : ℝ => x^2*hat x + (2*j)*(x*hat x) + j^2*hat x) := by
    funext x; ring
  rw [heq]
  have hi1 : Integrable (fun x : ℝ => x*hat x) := by simpa using integrable_pow_mul_hat 1
  exact ((integrable_pow_mul_hat 2).add (hi1.const_mul (2*j))).add (integrable_hat.const_mul (j^2))

private theorem integral_shifted_sq_hat (j : ℝ) :
    (∫ x : ℝ, (x+j)^2 * hat x) = j^2+1/6 := by
  have heq : (fun x : ℝ => (x+j)^2 * hat x) =
      (fun x : ℝ => x^2*hat x + (2*j)*(x*hat x) + j^2*hat x) := by
    funext x; ring
  have hi1 : Integrable (fun x : ℝ => x*hat x) := by simpa using integrable_pow_mul_hat 1
  rw [heq, integral_add (f := fun x : ℝ => x^2*hat x + (2*j)*(x*hat x)) (g := fun x : ℝ => j^2*hat x)
    ((integrable_pow_mul_hat 2).add (hi1.const_mul (2*j))) (integrable_hat.const_mul (j^2)),
    integral_add (f := fun x : ℝ => x^2*hat x) (g := fun x : ℝ => (2*j)*(x*hat x)) (integrable_pow_mul_hat 2) (hi1.const_mul (2*j)),
    integral_const_mul, integral_const_mul, integral_sq_mul_hat, integral_id_mul_hat,
    integral_hat]
  ring

theorem integrable_sq_mul_scaled_shifted_hat (m j : ℝ) (hm : m ≠ 0) :
    Integrable (fun v : ℝ => v^2 * hat (m*v-j)) := by
  have h := (((integrable_shifted_sq_hat j).comp_sub_right j).comp_mul_left' hm).const_mul (m⁻¹^2)
  convert h using 1
  funext v
  field_simp
  <;> ring

theorem integral_sq_mul_scaled_shifted_hat (m j : ℝ) (hm : 0 < m) :
    (∫ v : ℝ, v^2 * hat (m*v-j)) = (j^2+1/6)/m^3 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have heq : (fun v : ℝ => v^2 * hat (m*v-j)) =
      (fun v : ℝ => m⁻¹^2 * (((m*v-j)+j)^2 * hat (m*v-j))) := by
    funext v
    field_simp
    <;> ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => ((x-j)+j)^2 * hat (x-j)) m,
    integral_sub_right_eq_self (fun x : ℝ => (x+j)^2*hat x), integral_shifted_sq_hat]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hm)]
  field_simp
  <;> ring

theorem integral_affineSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    (∫ v : ℝ, affineSpectrum nodes m v) = nodalF0 nodes m := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hi (j : ℕ) : Integrable (fun v : ℝ =>
      node nodes j * (hat ((m:ℝ)*v-j) + hat ((m:ℝ)*v+j))) := by
    exact ((integrable_scaled_shifted_hat m j hm'.ne').add
      (by simpa [sub_neg_eq_add] using integrable_scaled_shifted_hat m (-(j:ℝ)) hm'.ne')).const_mul _
  have hi0 : Integrable (fun v : ℝ => hat ((m:ℝ)*v)) := by
    simpa using integrable_scaled_shifted_hat m 0 hm'.ne'
  have hip (j : ℕ) : Integrable (fun v : ℝ => hat ((m:ℝ)*v+j)) := by
    simpa [sub_neg_eq_add] using integrable_scaled_shifted_hat m (-(j:ℝ)) hm'.ne'
  have hp (j : ℕ) : (∫ v : ℝ, hat ((m:ℝ)*v+j)) = 1/(m:ℝ) := by
    simpa [sub_neg_eq_add] using integral_scaled_shifted_hat m (-(j:ℝ)) hm'
  have hpair (j : ℕ) : (∫ v : ℝ,
      node nodes j * (hat ((m:ℝ)*v-j) + hat ((m:ℝ)*v+j))) =
      node nodes j * (2/(m:ℝ)) := by
    rw [integral_const_mul, integral_add (integrable_scaled_shifted_hat m j hm'.ne') (hip j),
      integral_scaled_shifted_hat m j hm', hp]
    ring
  unfold affineSpectrum nodalF0
  rw [integral_add (hi0.const_mul _) (integrable_finsetSum _ (fun j hj => hi j)),
    integral_const_mul, integral_finsetSum _ (fun j hj => hi j)]
  simp_rw [hpair]
  rw [show (∫ v : ℝ, hat ((m:ℝ)*v)) = 1/(m:ℝ) by simpa using integral_scaled_shifted_hat m 0 hm']
  rw [← Finset.sum_mul]
  ring

/-- The absolute coefficient envelope is an actual integrable function, not a
numerical assumption about the Fourier transform. -/
def absoluteSpectrum (nodes : List ℚ) (m : ℕ) (v : ℝ) : ℝ :=
  |node nodes 0| * hat ((m:ℝ)*v) + ∑ j ∈ Finset.Ico 1 (nodes.length-1),
    |node nodes j| * (hat ((m:ℝ)*v-j) + hat ((m:ℝ)*v+j))

theorem abs_affineSpectrum_le_absoluteSpectrum (nodes : List ℚ) (m : ℕ) (v : ℝ) :
    |affineSpectrum nodes m v| ≤ absoluteSpectrum nodes m v := by
  unfold affineSpectrum absoluteSpectrum
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, abs_of_nonneg (hat_nonneg _)]
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul, abs_of_nonneg (add_nonneg (hat_nonneg _) (hat_nonneg _))]

theorem integrable_absoluteSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    Integrable (absoluteSpectrum nodes m) := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold absoluteSpectrum
  apply Integrable.add
  · simpa only [sub_zero] using (integrable_scaled_shifted_hat m 0 hm').const_mul |node nodes 0|
  · apply integrable_finsetSum
    intro j hj
    exact ((integrable_scaled_shifted_hat m j hm').add
      (by simpa [sub_neg_eq_add] using integrable_scaled_shifted_hat m (-(j:ℝ)) hm')).const_mul _

theorem integral_absoluteSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m) :
    (∫ v : ℝ, absoluteSpectrum nodes m v) = nodalMassA0 nodes m := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hi0 : Integrable (fun v : ℝ => hat ((m:ℝ)*v)) := by
    simpa using integrable_scaled_shifted_hat m 0 hm'.ne'
  have hip (j : ℕ) : Integrable (fun v : ℝ => hat ((m:ℝ)*v+j)) := by
    simpa [sub_neg_eq_add] using integrable_scaled_shifted_hat m (-(j:ℝ)) hm'.ne'
  have hi (j : ℕ) : Integrable (fun v : ℝ =>
      |node nodes j| * (hat ((m:ℝ)*v-j) + hat ((m:ℝ)*v+j))) :=
    ((integrable_scaled_shifted_hat m j hm'.ne').add (hip j)).const_mul _
  have hp (j : ℕ) : (∫ v : ℝ, hat ((m:ℝ)*v+j)) = 1/(m:ℝ) := by
    simpa [sub_neg_eq_add] using integral_scaled_shifted_hat m (-(j:ℝ)) hm'
  have hpair (j : ℕ) : (∫ v : ℝ,
      |node nodes j| * (hat ((m:ℝ)*v-j) + hat ((m:ℝ)*v+j))) =
      |node nodes j| * (2/(m:ℝ)) := by
    rw [integral_const_mul, integral_add (integrable_scaled_shifted_hat m j hm'.ne') (hip j),
      integral_scaled_shifted_hat m j hm', hp]
    ring
  unfold absoluteSpectrum nodalMassA0
  rw [integral_add (hi0.const_mul _) (integrable_finsetSum _ (fun j hj => hi j)),
    integral_const_mul, integral_finsetSum _ (fun j hj => hi j)]
  simp_rw [hpair]
  rw [show (∫ v : ℝ, hat ((m:ℝ)*v)) = 1/(m:ℝ) by simpa using integral_scaled_shifted_hat m 0 hm']
  rw [← Finset.sum_mul]
  ring

theorem integral_abs_affineSpectrum_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) :
    (∫ v : ℝ, |affineSpectrum nodes m v|) ≤ nodalMassA0 nodes m := by
  rw [← integral_absoluteSpectrum nodes m hm]
  exact integral_mono (integrable_affineSpectrum nodes m hlen hm).abs
    (integrable_absoluteSpectrum nodes m hm) (abs_affineSpectrum_le_absoluteSpectrum nodes m)

end RH080Next.Explicit
