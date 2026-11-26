import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace RH080Next.Primal

/-- Scaling under the actual Mathlib Fourier transform, with no numerical input. -/
theorem fourier_dilate (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    𝓕 (fun x : ℝ => f (s*x)) t = (s : ℂ)⁻¹ * 𝓕 f (t/s) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let g : ℝ → ℂ := fun y =>
    Complex.exp ((-2*Real.pi*(y*(t/s)) : ℝ) * Complex.I) • f y
  have h : (fun x : ℝ =>
      Complex.exp ((-2*Real.pi*inner ℝ x t : ℝ) * Complex.I) • f (s*x)) =
      fun x : ℝ => g (s*x) := by
    funext x
    dsimp [g]
    congr 2
    simp only [starRingEnd_apply, star_trivial]
    congr 1
    norm_cast
    field_simp [ne_of_gt hs]
  rw [h, MeasureTheory.Measure.integral_comp_mul_left g s]
  simp only [abs_of_pos (inv_pos.mpr hs), smul_eq_mul]
  rw [Complex.real_smul, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp [g, RCLike.inner_apply, mul_comm]

/-- Exact whole-line norm rescaling for real functions. -/
theorem norm_dilate (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, |f (s*x)|) = s⁻¹ * ∫ x : ℝ, |f x| := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => |f x|) s
  simpa only [abs_of_pos (inv_pos.mpr hs), smul_eq_mul] using h

/-- Integrability of the scaled candidate follows from the actual function. -/
theorem integrable_dilate {f : ℝ → ℂ} (h : Integrable f) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => f (s*x)) :=
  h.comp_mul_left' (ne_of_gt hs)

/-- Transport an established Fourier pair; no synthetic Fourier partner is assumed. -/
theorem fourier_pair_dilate (f g : ℝ → ℝ)
    (h : ∀ t : ℝ, 𝓕 (fun x : ℝ => (f x : ℂ)) t = (g t : ℂ))
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    𝓕 (fun x : ℝ => (f (s*x) : ℂ)) t = ((s⁻¹ * g (t/s) : ℝ) : ℂ) := by
  have hf := fourier_dilate (fun x : ℝ => (f x : ℂ)) hs t
  rw [h] at hf
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv] using hf

#print axioms fourier_dilate
#print axioms norm_dilate
#print axioms integrable_dilate
#print axioms fourier_pair_dilate
end RH080Next.Primal
