import GaussianActualTransform

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Real Polynomial MeasureTheory
open scoped FourierTransform
namespace RHOnePrime.GaussianFourier
open RHOnePrime.GaussianKernel

lemma complex_eval_coeffPoly (cs : List ℚ) (u : ℝ) :
    (coeffPoly cs).eval₂ (Rat.castHom ℂ) (u : ℂ) = (coeffEval cs u : ℂ) := by
  induction cs with
  | nil => simp [coeffPoly, coeffEval]
  | cons c cs ih =>
    simp [coeffPoly, coeffEval, ih]

lemma polyWave_map_coeffPoly (cs : List ℚ) :
    polyWave ((coeffPoly cs).map (Rat.castHom ℂ)) = sourceWave cs := by
  funext x
  simp only [polyWave, sourceWave, Polynomial.eval_map, complex_eval_coeffPoly]

lemma actual_source_transform :
    transformSource normSource = (coeffPoly wingSource).map (Rat.castHom ℂ) := by
  have h := transform_evenSource normEvenSource
  rw [actual_even_expansion, transformSource_append_zero, actual_even_transform] at h
  exact h

lemma sourceWave_physicalF : sourceWave normSource = fun x : ℝ => (physicalF x : ℂ) := by
  funext x
  simp [sourceWave, physicalF, scale, gaussian, mul_pow, Real.sq_sqrt Real.pi_pos.le]

lemma sourceWave_physicalG : sourceWave wingSource = fun x : ℝ => (physicalG x : ℂ) := by
  funext x
  simp [sourceWave, physicalG, scale, gaussian, mul_pow, Real.sq_sqrt Real.pi_pos.le]

/-- Genuine Fourier identity of the actual degree12 Laguerre / degree24
monomial witness. The transform is the actual integral, not an assumed pair. -/
theorem fourier_actual_physical :
    𝓕 (fun x : ℝ => (physicalF x : ℂ)) = fun x : ℝ => (physicalG x : ℂ) := by
  rw [← sourceWave_physicalF, fourier_sourceWave, actual_source_transform,
    polyWave_map_coeffPoly, sourceWave_physicalG]

theorem integrable_complex_physicalF : Integrable (fun x : ℝ => (physicalF x : ℂ)) := by
  rw [← sourceWave_physicalF]
  exact integrable_sourceWave normSource

theorem integrable_complex_physicalG : Integrable (fun x : ℝ => (physicalG x : ℂ)) := by
  rw [← sourceWave_physicalG]
  exact integrable_sourceWave wingSource

theorem integrable_physicalF : Integrable physicalF := by
  simpa using integrable_complex_physicalF.re

theorem integrable_physicalG : Integrable physicalG := by
  simpa using integrable_complex_physicalG.re

theorem continuous_physicalF : Continuous physicalF := by
  unfold physicalF
  exact ((continuous_coeffEval normSource).comp (continuous_const.mul continuous_id)).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).pow 2).neg)

theorem continuous_physicalG : Continuous physicalG := by
  unfold physicalG
  exact ((continuous_coeffEval wingSource).comp (continuous_const.mul continuous_id)).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).pow 2).neg)

theorem physicalF_even : Function.Even physicalF := by
  intro x
  simp only [physicalF, mul_neg, neg_sq, normSource_even]

theorem physicalG_even : Function.Even physicalG := by
  intro x
  simp only [physicalG, mul_neg, neg_sq, wingSource_even]

#print axioms fourier_actual_physical
#print axioms integrable_physicalF
#print axioms integrable_physicalG
#print axioms continuous_physicalF
#print axioms physicalF_even
end RHOnePrime.GaussianFourier
