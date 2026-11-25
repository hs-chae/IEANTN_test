/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FourierWeakDuality
import CosineChord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
namespace RH080.Dual

def box (r v : ℝ) : ℝ := (Icc (-r) r).indicator (fun _ => 1) v

lemma box_eq (r v : ℝ) : box r v = if |v| ≤ r then 1 else 0 := by
  simp only [box, Set.indicator_apply, mem_Icc, ← abs_le]

lemma box_nonneg (r v : ℝ) : 0 ≤ box r v := by
  rw [box_eq]
  split <;> norm_num

lemma box_le_one (r v : ℝ) : box r v ≤ 1 := by
  rw [box_eq]
  split <;> norm_num

lemma box_mono {r s : ℝ} (hrs : r ≤ s) (v : ℝ) : box r v ≤ box s v := by
  rw [box_eq, box_eq]
  split_ifs with h h' h' <;> try norm_num
  exact False.elim (h' (h.trans hrs))

lemma box_integrable (r : ℝ) : Integrable (box r) := by
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma box_mul_integrable (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) :
    Integrable (fun v : ℝ => box r v * f v) := by
  have hi : IntegrableOn f (Icc (-r) r) volume := hf.integrableOn_Icc
  have he : (fun v : ℝ => box r v * f v) = (Icc (-r) r).indicator f := by
    funext v
    by_cases hv : v ∈ Icc (-r) r <;> simp [box, hv]
  rw [he]
  exact hi.integrable_indicator measurableSet_Icc

lemma integral_box_mul (f : ℝ → ℝ) (r : ℝ) :
    (∫ v : ℝ, box r v * f v) = ∫ v in Icc (-r) r, f v := by
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext v
  by_cases hv : v ∈ Icc (-r) r <;> simp [box, hv]

lemma box_moment (r : ℝ) (hr : 0 ≤ r) :
    (∫ v : ℝ, box r v * v ^ 2) = 2 * r ^ 3 / 3 := by
  rw [integral_box_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r), integral_pow]
  ring

lemma cosineTransform_box (r x : ℝ) (hr : 0 ≤ r) (hx : x ≠ 0) :
    cosineTransform (box r) x = sin (2*π*r*x)/(π*x) := by
  unfold cosineTransform
  rw [integral_box_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hfreq : 2*π*x ≠ 0 := by positivity
  have hi : (∫ v : ℝ in -r..r, cos (2*π*v*x)) =
      sin (2*π*r*x)/(2*π*x)-sin (2*π*(-r)*x)/(2*π*x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v : ℝ => sin (2*π*v*x)/(2*π*x))
      (f' := fun v : ℝ => cos (2*π*v*x))
    · intro v _
      have hh := (((hasDerivAt_id v).const_mul (2*π)).mul_const x).sin.div_const (2*π*x)
      simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ hfreq] using hh
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hi]
  rw [show 2*π*(-r)*x = -(2*π*r*x) by ring, sin_neg]
  field_simp
  ring

def height : ℕ → ℤ
  | 0 => 256 | 1 => 256 | 2 => 256 | 3 => 256 | 4 => -581
  | 5 => 40 | 6 => 169 | 7 => -82 | 8 => 147 | 9 => -102
  | 10 => 68 | 11 => -108 | 12 => 11 | 13 => 34 | 14 => 49
  | 15 => -62 | 16 => 41 | 17 => -41 | 18 => 18 | _ => 0

def stepCell (j : ℕ) (v : ℝ) : ℝ :=
  if j = 0 then box (1/4) v else box ((j+1)/4) v-box (j/4) v

def compactStep (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20, ((height j : ℝ)/256) * stepCell j v

def jumpCoeff (j : ℕ) : ℤ := height j - height (j+1)

lemma stepCell_nonneg (j : ℕ) (v : ℝ) : 0 ≤ stepCell j v := by
  unfold stepCell
  split_ifs with hj
  · exact box_nonneg _ _
  · exact sub_nonneg.mpr (box_mono (by push_cast; linarith) v)

lemma stepCell_integrable (j : ℕ) : Integrable (stepCell j) := by
  unfold stepCell
  split_ifs with hj
  · exact box_integrable _
  · exact (box_integrable _).sub (box_integrable _)

lemma stepCell_sum (v : ℝ) : (∑ j ∈ Finset.range 20, stepCell j v) = box 5 v := by
  norm_num [Finset.sum_range_succ, stepCell]

lemma compactStep_integrable : Integrable compactStep := by
  apply integrable_finset_sum
  intro j _
  exact (stepCell_integrable j).const_mul _

lemma compactStep_jump (v : ℝ) : compactStep v =
    ∑ j ∈ Finset.range 20, ((jumpCoeff j : ℝ)/256) * box ((j+1)/4) v := by
  norm_num [compactStep, jumpCoeff, height, stepCell, Finset.sum_range_succ]
  ring

lemma height_bounds (j : ℕ) (hj : j < 20) :
    (1 - (36/11 : ℝ)) ≤ (height j : ℝ)/256 ∧ (height j : ℝ)/256 ≤ 1 := by
  interval_cases j <;> norm_num [height]

lemma compactStep_bounds (v : ℝ) :
    1-(36/11 : ℝ) ≤ compactStep v ∧ compactStep v ≤ 1 := by
  have hl : (1-(36/11 : ℝ))*(∑ j ∈ Finset.range 20, stepCell j v) ≤ compactStep v := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (height_bounds j (Finset.mem_range.mp hj)).1
      (stepCell_nonneg j v)
  have hu : compactStep v ≤ ∑ j ∈ Finset.range 20, stepCell j v := by
    apply Finset.sum_le_sum
    intro j hj
    exact (mul_le_mul_of_nonneg_right (height_bounds j (Finset.mem_range.mp hj)).2
      (stepCell_nonneg j v)).trans_eq (one_mul _)
  rw [stepCell_sum] at hl hu
  constructor
  · have hbox := box_le_one 5 v
    nlinarith
  · exact hu.trans (box_le_one 5 v)

lemma compactStep_center (v : ℝ) (hv : |v| ≤ 1) : compactStep v = 1 := by
  have hb (r : ℝ) (hr : 1 ≤ r) : box r v = 1 := by
    rw [box_eq, if_pos (hv.trans hr)]
  norm_num [compactStep, height, stepCell, Finset.sum_range_succ, hb] <;> ring

def compactNumerator (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20, ((jumpCoeff j : ℝ)/256) * sin (π*(j+1)*x/2)

lemma stepCell_moment_integrable (j : ℕ) :
    Integrable (fun v : ℝ => stepCell j v * v^2) := by
  unfold stepCell
  split_ifs with hj
  · exact box_mul_integrable (fun v : ℝ => v^2) (by fun_prop) _
  · have hi := (box_mul_integrable (fun v : ℝ => v^2) (by fun_prop) ((j+1)/4)).sub
      (box_mul_integrable (fun v : ℝ => v^2) (by fun_prop) (j/4))
    have he : (fun v : ℝ => (box ((j+1)/4) v - box (j/4) v)*v^2) =
        ((fun v : ℝ => box ((j+1)/4) v * v^2) - (fun v : ℝ => box (j/4) v * v^2)) := by
      funext v
      simp only [Pi.sub_apply]
      ring
    rw [he]
    exact hi

lemma stepCell_moment (j : ℕ) :
    (∫ v : ℝ, stepCell j v * v^2) =
      2/3 * (((j+1 : ℕ) : ℝ)^3-(j : ℝ)^3)/64 := by
  unfold stepCell
  split_ifs with hj
  · subst j
    norm_num [box_moment]
  · have hi := integral_sub
      (box_mul_integrable (fun v : ℝ => v^2) (by fun_prop) ((j+1)/4))
      (box_mul_integrable (fun v : ℝ => v^2) (by fun_prop) (j/4))
    have he : (fun v : ℝ => (box ((j+1)/4) v - box (j/4) v)*v^2) =
      (fun v : ℝ => box ((j+1)/4) v * v^2-box (j/4) v*v^2) := by
      funext v
      ring
    rw [he, hi, box_moment _ (by positivity), box_moment _ (by positivity)]
    push_cast
    ring

lemma abs_compactStep_le (v : ℝ) :
    |compactStep v| ≤ ∑ j ∈ Finset.range 20, |(height j : ℝ)/256| * stepCell j v := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_of_nonneg (stepCell_nonneg j v)]

def momentEnvelope (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20, |(height j : ℝ)/256| * (stepCell j v * v^2)

lemma momentEnvelope_integrable : Integrable momentEnvelope := by
  apply integrable_finsetSum
  intro j _
  exact (stepCell_moment_integrable j).const_mul _

lemma momentEnvelope_nonneg (v : ℝ) : 0 ≤ momentEnvelope v := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (abs_nonneg _) (mul_nonneg (stepCell_nonneg j v) (sq_nonneg v))

lemma momentEnvelope_majorizes (v : ℝ) : |compactStep v| *v^2 ≤ momentEnvelope v := by
  have h := mul_le_mul_of_nonneg_right (abs_compactStep_le v) (sq_nonneg v)
  simpa [momentEnvelope, Finset.sum_mul, mul_assoc] using h

lemma compactStep_moment_integrable : Integrable (fun v : ℝ => |compactStep v| * v^2) := by
  apply momentEnvelope_integrable.mono
  · exact compactStep_integrable.norm.aestronglyMeasurable.mul
      (show AEStronglyMeasurable (fun v : ℝ => v^2) volume from
        (by fun_prop : Continuous (fun v : ℝ => v^2)).aestronglyMeasurable)
  · filter_upwards with v
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg (compactStep v)) (sq_nonneg v)),
      abs_of_nonneg (momentEnvelope_nonneg v)] using momentEnvelope_majorizes v

lemma momentEnvelope_integral :
    (∫ v : ℝ, momentEnvelope v) = (134917 / 8192 : ℝ) := by
  unfold momentEnvelope
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, stepCell_moment]
    norm_num [Finset.sum_range_succ, height]
  · intro j _
    exact (stepCell_moment_integrable j).const_mul _

lemma compactStep_moment_le :
    (∫ v : ℝ, |compactStep v| *v^2) ≤ (134917 / 8192 : ℝ) := by
  rw [← momentEnvelope_integral]
  exact integral_mono compactStep_moment_integrable momentEnvelope_integrable
    momentEnvelope_majorizes

lemma cosineTransform_box_zero (r : ℝ) (hr : 0 ≤ r) :
    cosineTransform (box r) 0 = 2*r := by
  unfold cosineTransform
  simp only [mul_zero, cos_zero, mul_one]
  have hi := integral_box_mul (fun _ : ℝ => 1) r
  simp only [mul_one] at hi
  rw [hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  simp
  ring

lemma compact_kernel_eq_sum (x : ℝ) :
    cosineTransform compactStep x =
      ∑ j ∈ Finset.range 20, ((jumpCoeff j : ℝ)/256) *
        cosineTransform (box ((j+1)/4)) x := by
  unfold cosineTransform
  have he : (fun v : ℝ => compactStep v * cos (2*π*v*x)) =
      (fun v : ℝ => ∑ j ∈ Finset.range 20,
        ((jumpCoeff j : ℝ)/256)*(box ((j+1)/4) v * cos (2*π*v*x))) := by
    funext v
    rw [compactStep_jump, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro j _
    exact (box_mul_integrable (fun v : ℝ => cos (2*π*v*x)) (by fun_prop) _).const_mul _

lemma compact_kernel_sine (x : ℝ) (hx : x ≠ 0) :
    cosineTransform compactStep x = compactNumerator x/(π*x) := by
  rw [compact_kernel_eq_sum]
  have hh (j : ℕ) : cosineTransform (box ((j+1)/4)) x =
      sin (2*π*((j+1)/4)*x)/(π*x) :=
    cosineTransform_box _ x (by positivity) hx
  simp_rw [hh]
  unfold compactNumerator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [show 2*π*((j+1)/4)*x = π*(j+1)*x/2 by ring]
  ring

lemma compact_kernel_zero : cosineTransform compactStep 0 = (625/512 : ℝ) := by
  rw [compact_kernel_eq_sum]
  have hh (j : ℕ) : cosineTransform (box ((j+1)/4)) 0 = 2*((j+1)/4) :=
    cosineTransform_box_zero _ (by positivity)
  simp_rw [hh]
  norm_num [Finset.sum_range_succ, jumpCoeff, height]

#print axioms compactStep_moment_le
#print axioms compact_kernel_sine
#print axioms compact_kernel_zero

end RH080.Dual
