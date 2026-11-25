/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Primal80CoefficientTransform
import G40Functions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Polynomial MeasureTheory
open scoped FourierTransform
namespace RH080.Primal80Fourier
open RHOnePrime.GaussianFourier

lemma coefficient_eval_identity (cs : List ℚ) (u : ℝ) :
    RHOnePrime.GaussianKernel.coeffEval cs u = RH080.Gaussian40.coeffEval cs u := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [RHOnePrime.GaussianKernel.coeffEval, RH080.Gaussian40.coeffEval, ih]

lemma complex_eval_coeffPoly (cs : List ℚ) (u : ℝ) :
    (RHOnePrime.GaussianKernel.coeffPoly cs).eval₂ (Rat.castHom ℂ) (u : ℂ) =
      (RHOnePrime.GaussianKernel.coeffEval cs u : ℂ) := by
  induction cs with
  | nil => simp [RHOnePrime.GaussianKernel.coeffPoly, RHOnePrime.GaussianKernel.coeffEval]
  | cons c cs ih =>
    simp [RHOnePrime.GaussianKernel.coeffPoly, RHOnePrime.GaussianKernel.coeffEval, ih]

lemma polyWave_map_coeffPoly (cs : List ℚ) :
    polyWave ((RHOnePrime.GaussianKernel.coeffPoly cs).map (Rat.castHom ℂ)) =
      sourceWave cs := by
  funext x
  simp only [polyWave, sourceWave, Polynomial.eval_map, complex_eval_coeffPoly]

lemma sourceWave_physicalF : sourceWave RH080.Gaussian40.normSource =
    fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ) := by
  funext x
  simp [sourceWave, RH080.Gaussian40.physicalF, scale, gaussian,
    coefficient_eval_identity, mul_pow, Real.sq_sqrt Real.pi_pos.le]

lemma sourceWave_physicalG : sourceWave RH080.Gaussian40.wingSource =
    fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ) := by
  funext x
  simp [sourceWave, RH080.Gaussian40.physicalG, scale, gaussian,
    coefficient_eval_identity, mul_pow, Real.sq_sqrt Real.pi_pos.le]

/-- True Mathlib integral Fourier identity of the frozen degree40Laguerre /
degree80physical witness. Fourier convention is exp(-2πixv). No Fourier-pair
predicate, numerical integral certificate, RH, or CMS source premise is assumed. -/
theorem fourier_actual_physical :
    𝓕 (fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ)) =
      fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ) := by
  rw [←sourceWave_physicalF, fourier_sourceWave, actual_source_transform,
    polyWave_map_coeffPoly, sourceWave_physicalG]

theorem integrable_complex_physicalF :
    Integrable (fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ)) := by
  rw [←sourceWave_physicalF]
  exact integrable_sourceWave RH080.Gaussian40.normSource

theorem integrable_complex_physicalG :
    Integrable (fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ)) := by
  rw [←sourceWave_physicalG]
  exact integrable_sourceWave RH080.Gaussian40.wingSource

theorem integrable_physicalF : Integrable RH080.Gaussian40.physicalF := by
  simpa using integrable_complex_physicalF.re

theorem integrable_physicalG : Integrable RH080.Gaussian40.physicalG := by
  simpa using integrable_complex_physicalG.re

theorem continuous_physicalF : Continuous RH080.Gaussian40.physicalF := by
  unfold RH080.Gaussian40.physicalF
  exact ((RH080.Gaussian40.continuous_coeffEval RH080.Gaussian40.normSource).comp
    (continuous_const.mul continuous_id)).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).pow 2).neg)

theorem continuous_physicalG : Continuous RH080.Gaussian40.physicalG := by
  unfold RH080.Gaussian40.physicalG
  exact ((RH080.Gaussian40.continuous_coeffEval RH080.Gaussian40.wingSource).comp
    (continuous_const.mul continuous_id)).mul
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).pow 2).neg)

lemma coeffEval_append_zero (cs : List ℚ) (u : ℝ) :
    RHOnePrime.GaussianKernel.coeffEval (cs++[0]) u =
      RHOnePrime.GaussianKernel.coeffEval cs u := by
  induction cs with
  | nil => simp [RHOnePrime.GaussianKernel.coeffEval]
  | cons c cs ih => simp [RHOnePrime.GaussianKernel.coeffEval, ih]

lemma coeffEval_evenSource (cs : List ℚ) (u : ℝ) :
    RHOnePrime.GaussianKernel.coeffEval (evenSource cs) (-u) =
      RHOnePrime.GaussianKernel.coeffEval (evenSource cs) u := by
  induction cs with
  | nil => simp [evenSource, RHOnePrime.GaussianKernel.coeffEval]
  | cons c cs ih =>
    simp only [evenSource, RHOnePrime.GaussianKernel.coeffEval, Rat.cast_zero, ih]
    ring

theorem normSource_even (u : ℝ) :
    RH080.Gaussian40.coeffEval RH080.Gaussian40.normSource (-u) =
      RH080.Gaussian40.coeffEval RH080.Gaussian40.normSource u := by
  rw [←coefficient_eval_identity, ←coefficient_eval_identity,
    ←coeffEval_append_zero RH080.Gaussian40.normSource (-u),
    ←coeffEval_append_zero RH080.Gaussian40.normSource u, ←actual_norm_expansion]
  exact coeffEval_evenSource normEvenSource u

theorem wingSource_even (u : ℝ) :
    RH080.Gaussian40.coeffEval RH080.Gaussian40.wingSource (-u) =
      RH080.Gaussian40.coeffEval RH080.Gaussian40.wingSource u := by
  rw [←coefficient_eval_identity, ←coefficient_eval_identity,
    ←coeffEval_append_zero RH080.Gaussian40.wingSource (-u),
    ←coeffEval_append_zero RH080.Gaussian40.wingSource u, ←actual_wing_expansion]
  exact coeffEval_evenSource wingEvenSource u

theorem physicalF_even : Function.Even RH080.Gaussian40.physicalF := by
  intro x
  simp only [RH080.Gaussian40.physicalF, mul_neg, neg_sq, normSource_even]

theorem physicalG_even : Function.Even RH080.Gaussian40.physicalG := by
  intro x
  simp only [RH080.Gaussian40.physicalG, mul_neg, neg_sq, wingSource_even]

#print axioms fourier_actual_physical
#print axioms integrable_physicalF
#print axioms integrable_physicalG
#print axioms continuous_physicalF
#print axioms continuous_physicalG
#print axioms physicalF_even
#print axioms physicalG_even
end RH080.Primal80Fourier
