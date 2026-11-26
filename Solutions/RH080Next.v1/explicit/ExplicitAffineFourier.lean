/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineIntegrals
import ExplicitHatFourier
import ExplicitCosineMoment

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem integrable_hat : Integrable hat := by simpa using integrable_pow_mul_hat 0

private theorem integrable_hat_mul_cos (t : ℝ) :
    Integrable (fun v : ℝ => hat v * cos (t*v)) := by
  apply integrable_hat.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with v
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*v)

private theorem integrable_hat_mul_sin (t : ℝ) :
    Integrable (fun v : ℝ => hat v * sin (t*v)) := by
  apply integrable_hat.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with v
    simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t*v)

theorem integral_hat_mul_sin (t : ℝ) : (∫ v : ℝ, hat v * sin (t*v)) = 0 := by
  have h := integral_neg_eq_self (fun v : ℝ => hat v * sin (t*v)) volume
  have heq : (fun v : ℝ => hat (-v)*sin (t*(-v))) =
      (fun v : ℝ => -(hat v*sin (t*v))) := by
    funext v
    simp [hat_neg]
  rw [heq, integral_neg] at h
  linarith

/-- Scaling and translation are proved for the actual cosine integral. -/
theorem integral_shifted_hat_cos (m j t : ℝ) (hm : 0 < m) :
    (∫ v : ℝ, hat (m*v-j)*cos (t*v)) =
      cos (t*j/m)/m * (∫ v : ℝ, hat v*cos ((t/m)*v)) := by
  have hm0 := hm.ne'
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ => hat (x-j)*cos ((t/m)*x)) m
  have hscaleeq : (fun v : ℝ => hat (m*v-j)*cos ((t/m)*(m*v))) =
      (fun v : ℝ => hat (m*v-j)*cos (t*v)) := by
    funext v
    congr 2
    field_simp
  rw [hscaleeq] at hscale
  rw [hscale]
  have hshift : (∫ x : ℝ, hat ((x+j)-j)*cos ((t/m)*(x+j))) =
      (∫ x : ℝ, hat (x-j)*cos ((t/m)*x)) :=
    integral_add_right_eq_self (fun x : ℝ => hat (x-j)*cos ((t/m)*x)) j
  rw [← hshift]
  have heq : (fun v : ℝ => hat ((v+j)-j)*cos ((t/m)*(v+j))) =
      (fun v : ℝ => cos (t*j/m)*(hat v*cos ((t/m)*v)) -
        sin (t*j/m)*(hat v*sin ((t/m)*v))) := by
    funext v
    rw [add_sub_cancel_right, mul_add, show t/m*j = t*j/m by ring, cos_add]
    ring
  rw [heq, integral_sub ((integrable_hat_mul_cos (t/m)).const_mul _)
    ((integrable_hat_mul_sin (t/m)).const_mul _),
    integral_const_mul, integral_const_mul, integral_hat_mul_sin]
  simp only [mul_zero, sub_zero, smul_eq_mul, abs_of_pos (inv_pos.mpr hm)]
  ring

def nodalPolynomial (nodes : List ℚ) (y : ℝ) : ℝ :=
  node nodes 0 + 2*∑ j ∈ Finset.Ico 1 (nodes.length-1), node nodes j*cos (2*π*j*y)

/-- The finite nodal polynomial is linked to the actual transform. -/
theorem inverseCosine_affineSpectrum (nodes : List ℚ) (m : ℕ) (hm : 0 < m)
    (u : ℝ) :
    inverseCosine (affineSpectrum nodes m) u =
      (1/(m:ℝ)) * (∫ v : ℝ, hat v*cos ((2*π*u/(m:ℝ))*v)) *
        nodalPolynomial nodes (u/(m:ℝ)) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hi0 : Integrable (fun v : ℝ => hat ((m:ℝ)*v)) := by
    simpa using integrable_scaled_shifted_hat m 0 hm'.ne'
  have hip (j : ℕ) : Integrable (fun v : ℝ => hat ((m:ℝ)*v+j)) := by
    simpa [sub_neg_eq_add] using integrable_scaled_shifted_hat m (-(j:ℝ)) hm'.ne'
  have hi (j : ℕ) : Integrable (fun v : ℝ => node nodes j *
      (hat ((m:ℝ)*v-j)*cos (2*π*u*v) + hat ((m:ℝ)*v+j)*cos (2*π*u*v))) := by
    exact ((integrable_cosineIntegrand _ (integrable_scaled_shifted_hat m j hm'.ne') u).add
      (integrable_cosineIntegrand _ (hip j) u)).const_mul _
  have heq : (fun v : ℝ => affineSpectrum nodes m v*cos (2*π*u*v)) =
      (fun v : ℝ => node nodes 0*(hat ((m:ℝ)*v)*cos (2*π*u*v)) +
        ∑ j ∈ Finset.Ico 1 (nodes.length-1), node nodes j*
          (hat ((m:ℝ)*v-j)*cos (2*π*u*v) + hat ((m:ℝ)*v+j)*cos (2*π*u*v))) := by
    funext v
    simp only [affineSpectrum, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  unfold inverseCosine
  rw [heq, integral_add ((integrable_cosineIntegrand _ hi0 u).const_mul _)
    (integrable_finsetSum _ (fun j hj => hi j)), integral_const_mul,
    integral_finsetSum _ (fun j hj => hi j)]
  have hp (j : ℕ) : (∫ v : ℝ, node nodes j*
      (hat ((m:ℝ)*v-j)*cos (2*π*u*v) + hat ((m:ℝ)*v+j)*cos (2*π*u*v))) =
      2*node nodes j*cos (2*π*j*(u/(m:ℝ)))/(m:ℝ) *
        (∫ v : ℝ, hat v*cos ((2*π*u/(m:ℝ))*v)) := by
    rw [integral_const_mul, integral_add
      (integrable_cosineIntegrand _ (integrable_scaled_shifted_hat m j hm'.ne') u)
      (integrable_cosineIntegrand _ (hip j) u),
      integral_shifted_hat_cos m j (2*π*u) hm',
      show (∫ v : ℝ, hat ((m:ℝ)*v+j)*cos (2*π*u*v)) =
        cos ((2*π*u)*(-(j:ℝ))/(m:ℝ))/(m:ℝ) * (∫ v : ℝ, hat v*cos ((2*π*u/(m:ℝ))*v)) by
        simpa [sub_neg_eq_add] using integral_shifted_hat_cos m (-(j:ℝ)) (2*π*u) hm']
    rw [show 2*π*u*(-(j:ℝ))/(m:ℝ) = -(2*π*u*j/(m:ℝ)) by ring, cos_neg,
      show 2*π*u*j/(m:ℝ) = 2*π*j*(u/(m:ℝ)) by ring]
    ring
  simp_rw [hp]
  rw [show (∫ v : ℝ, hat ((m:ℝ)*v)*cos (2*π*u*v)) =
    (1/(m:ℝ))*(∫ v : ℝ, hat v*cos ((2*π*u/(m:ℝ))*v)) by
    simpa using integral_shifted_hat_cos m 0 (2*π*u) hm']
  unfold nodalPolynomial
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Real Fourier normalization: mathlib's sinc is sin(x)/x. -/
theorem inverseCosine_affineSpectrum_sinc (nodes : List ℚ) (m : ℕ) (hm : 0 < m)
    (u : ℝ) :
    inverseCosine (affineSpectrum nodes m) u =
      (1/(m:ℝ)) * Real.sinc (π*u/(m:ℝ))^2 * nodalPolynomial nodes (u/(m:ℝ)) := by
  rw [inverseCosine_affineSpectrum nodes m hm, integral_hat_mul_cos_eq_sinc_sq]
  congr 2
  congr 1
  congr 1
  ring

/-- A change of mesh rescales the actual transform; this is also useful for
transporting published fixed-support analytic lemmas without adding a new
support-seven hypothesis. -/
theorem inverseCosine_affineSpectrum_mesh_dilation (nodes : List ℚ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (u : ℝ) :
    inverseCosine (affineSpectrum nodes m) u =
      ((n:ℝ)/(m:ℝ))*inverseCosine (affineSpectrum nodes n) (((n:ℝ)/(m:ℝ))*u) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inverseCosine_affineSpectrum_sinc nodes m hm,
    inverseCosine_affineSpectrum_sinc nodes n hn]
  have hp : ((n:ℝ)/(m:ℝ)*u)/(n:ℝ) = u/(m:ℝ) := by field_simp
  have hs : π*((n:ℝ)/(m:ℝ)*u)/(n:ℝ) = π*u/(m:ℝ) := by field_simp
  rw [hp, hs]
  field_simp
  <;> ring

end RH080Next.Explicit
