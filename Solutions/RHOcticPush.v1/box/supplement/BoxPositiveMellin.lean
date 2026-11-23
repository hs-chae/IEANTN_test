/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BoxFourierSeries
import BoxMellinNormalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
namespace RHOcticPush.BoxPositiveMellin
open Real MeasureTheory Set RHOcticPush.BoxFourierSeries
set_option maxHeartbeats 0

noncomputable def positiveTerm (n : ℕ+) (y : ℝ) : ℝ :=
  (1-Real.cos (2*(n:ℝ)*y))/(4*(n:ℝ)^2-1)

lemma positiveTerms_summable (y : ℝ) : Summable (fun n => positiveTerm n y) := by
  have h := weights_summable.sub (cosine_terms_summable y)
  exact h.congr (fun n => by simp only [positiveTerm,weight,sub_div])

noncomputable def term (s : ℝ) (n : ℕ+) (y : ℝ) : ℝ :=
  (4/Real.pi)*positiveTerm n y*y^(s-2)

lemma term_nonneg (s : ℝ) (n : ℕ+) {y : ℝ} (hy : 0<y) : 0≤term s n y := by
  exact mul_nonneg (mul_nonneg (by positivity) (positive_series_nonneg y n))
    (Real.rpow_nonneg hy.le _)

/-- Exact pointwise expansion of the actual Mellin integrand; no target moment
value or Gamma/Laurent identity is assumed. -/
lemma pointwise_hasSum (s : ℝ) {y : ℝ} (hy : 0<y) :
    HasSum (fun n => term s n y) (RHOcticPush.BoxMellin.mellinPacket s y) := by
  have h := ((positiveTerms_summable y).hasSum.mul_left (4/Real.pi)).mul_right (y^(s-2))
  simp only [positiveTerm] at h
  rw [←absolute_sine_positive_series y] at h
  convert! h using 1
  unfold RHOcticPush.BoxMellin.mellinPacket
  rw [abs_div,abs_of_pos hy]
  have hr : y^(s-1)=y^(s-2)*y := by
    rw [show s-1=(s-2)+1 by ring,Real.rpow_add hy,Real.rpow_one]
  rw [hr]
  field_simp [hy.ne']

lemma term_continuous (s : ℝ) (n : ℕ+) : ContinuousOn (term s n) (Ioi (0:ℝ)) := by
  apply ContinuousOn.mul
  · exact (by unfold positiveTerm; fun_prop : Continuous (fun y : ℝ => (4/Real.pi)*positiveTerm n y)).continuousOn
  · exact continuousOn_id.rpow_const (fun y hy => Or.inl (show 0<y from hy).ne')

/-- Justified infinite series/integral exchange on the ENTIRE genuine Mellin
strip. Nonnegativity and the previously proved actual Mellin integrability
provide domination, so this is not an unproved formal interchange. -/
theorem actual_mellin_as_series {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    HasSum (fun n : ℕ+ => ∫ y in Ioi (0:ℝ),term s n y)
      (RHOcticPush.BoxMellin.mellin s) := by
  apply hasSum_integral_of_dominated_convergence (term s)
  · intro n
    exact (term_continuous s n).aestronglyMeasurable measurableSet_Ioi
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (term_nonneg s n hy)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (pointwise_hasSum s hy).summable
  · apply (RHOcticPush.BoxMellin.mellin_integrable hs0 hs1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (pointwise_hasSum s hy).tsum_eq.symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact pointwise_hasSum s hy

#print axioms pointwise_hasSum
#print axioms actual_mellin_as_series
end RHOcticPush.BoxPositiveMellin
