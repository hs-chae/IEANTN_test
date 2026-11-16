import Formal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
noncomputable section
open Real MeasureTheory
namespace ExposureTask

lemma power_tail {x : ℝ} (hx : 0 < x) :
    (∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8)) = 8 * x ^ (-(1:ℝ)/8) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(9:ℝ)/8 < -1) hx]
  norm_num
  ring

lemma log_tail_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t ^ (-(9:ℝ)/8) / Real.log t) (Set.Ioi x) := by
  have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(9:ℝ)/8 < -1)
    (by linarith : 0 < x)).div_const (Real.log x)
  apply hg.mono' ((by fun_prop : Measurable (fun t : ℝ => t ^ (-(9:ℝ)/8) / Real.log t)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 < t := lt_trans hx ht
  have ht0 : 0 ≤ t := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg ht0 _)
    (Real.log_pos ht1).le)]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg ht0 _)
    (Real.log_pos hx) (Real.log_le_log (by linarith) ht.le)

lemma log_tail_bound {x : ℝ} (hx : 1 < x) :
    (∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log t) ≤
      8 * x ^ (-(1:ℝ)/8) / Real.log x := by
  have hg := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(9:ℝ)/8 < -1)
    (by linarith : 0 < x)).div_const (Real.log x)
  calc
    _ ≤ ∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log x := by
      apply integral_mono_ae (log_tail_integrable hx) hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change x < t at ht
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith : 0 ≤ t) _)
        (Real.log_pos hx) (Real.log_le_log (by linarith) ht.le)
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]
                simpa only [div_eq_mul_inv] using
                  congrArg (fun y : ℝ => y / Real.log x) (power_tail (by linarith : 0 < x))

/-- The only analytic hypothesis; not asserted as an axiom. -/
def PrimeCountingInput : Prop :=
  ∀ t : ℝ, Real.exp 300 ≤ t → Epi t ≤ C * t ^ (-(1:ℝ)/8)

lemma input_weight_bound (hP : PrimeCountingInput) {t : ℝ} (ht : Real.exp 300 ≤ t) :
    |(pi t - Li2 t) / t^2| ≤ C * (t ^ (-(9:ℝ)/8) / Real.log t) := by
  have h1 : 1 < t := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 300)) ht
  have ht0 : 0 < t := by linarith
  have hb := div_le_div_of_nonneg_right (error_bound_at ht (hP t ht))
    (sq_nonneg t)
  rw [abs_div, abs_of_nonneg (sq_nonneg t)]
  apply hb.trans_eq
  have hr : t ^ (-(9:ℝ)/8) = t ^ (-(1:ℝ)/8) / t := by
    convert Real.rpow_sub_one ht0.ne' (-(1:ℝ)/8) using 1 <;> norm_num
  rw [hr]
  field_simp

lemma actual_error_integrable (hP : PrimeCountingInput) {x : ℝ}
    (hx : Real.exp 300 ≤ x) :
    IntegrableOn (fun t : ℝ => (pi t - Li2 t) / t^2) (Set.Ioi x) := by
  have hA : (2:ℝ) ≤ Real.exp 300 := by
    have h := Real.add_one_le_exp (300:ℝ)
    linarith
  have hx1 : 1 < x := by linarith [hx.trans' hA]
  have hmP : Measurable pi := by
    unfold pi
    fun_prop
  have hcL : ContinuousOn Li2 (Set.Ioi x) := by
    intro t ht
    exact (Li2_hasDerivAt (by have htx : x < t := ht; linarith)).continuousAt.continuousWithinAt
  have hmL := hcL.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hg := (log_tail_integrable hx1).const_mul C
  have hm : AEStronglyMeasurable (fun t : ℝ => (pi t - Li2 t) / t^2)
      (volume.restrict (Set.Ioi x)) := by
    simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def] using (hmP.aestronglyMeasurable.sub hmL).mul
      ((by fun_prop : Measurable (fun t : ℝ => (t^2)⁻¹)).aestronglyMeasurable)
  apply hg.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact input_weight_bound hP (by have htx : x < t := ht; linarith)

lemma actual_tail_bound (hP : PrimeCountingInput) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    |∫ t in Set.Ioi x, (pi t - Li2 t) / t^2| ≤
      8 * C * x ^ (-(1:ℝ)/8) / Real.log x := by
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 300)) hx
  calc
    _ ≤ ∫ t in Set.Ioi x, |(pi t - Li2 t) / t^2| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioi x, C * (t ^ (-(9:ℝ)/8) / Real.log t) := by
      apply integral_mono_ae (actual_error_integrable hP hx).abs
        ((log_tail_integrable hx1).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact input_weight_bound hP (by have htx : x < t := ht; linarith)
    _ = C * (∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log t) := integral_const_mul _ _
    _ ≤ C * (8 * x ^ (-(1:ℝ)/8) / Real.log x) :=
      mul_le_mul_of_nonneg_left (log_tail_bound hx1) (by norm_num [C])
    _ = _ := by ring

def reciprocalConstant : ℝ :=
  -Real.log (Real.log 2) +
    (∫ t in (2:ℝ)..Real.exp 300, (pi t - Li2 t) / t^2) +
    ∫ t in Set.Ioi (Real.exp 300), (pi t - Li2 t) / t^2

lemma error_weight_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (pi t - Li2 t) / t^2) volume 2 x := by
  simp_rw [sub_div]
  exact (pi_weight_integrable hx).sub (Li2_weight_integrable hx)

theorem exact_tail_identity (hP : PrimeCountingInput) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    primeReciprocal x - Real.log (Real.log x) - reciprocalConstant =
      (pi x - Li2 x) / x - ∫ t in Set.Ioi x, (pi t - Li2 t) / t^2 := by
  have hA : (2:ℝ) ≤ Real.exp 300 := by linarith [Real.add_one_le_exp (300:ℝ)]
  have h1 := reciprocal_error_identity (hA.trans hx)
  have hiA := error_weight_integrable hA
  have hix := error_weight_integrable (hA.trans hx)
  have h2 := intervalIntegral.integral_add_adjacent_intervals hiA (hiA.symm.trans hix)
  have h3 := intervalIntegral.integral_interval_add_Ioi
    (actual_error_integrable hP (le_refl (Real.exp 300))) (actual_error_integrable hP hx)
  unfold reciprocalConstant
  linarith

lemma endpoint_error_bound (hP : PrimeCountingInput) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    |(pi x - Li2 x) / x| ≤ C * x ^ (-(1:ℝ)/8) / Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h := div_le_div_of_nonneg_right (error_bound_at hx (hP x hx)) hx0.le
  rw [abs_div, abs_of_pos hx0]
  apply h.trans_eq
  field_simp

/-- Whole-ray bound for the actual discrete prime-reciprocal sum. -/
theorem whole_ray_error (hP : PrimeCountingInput) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    |primeReciprocal x - Real.log (Real.log x) - reciprocalConstant| ≤
      9 * C * x ^ (-(1:ℝ)/8) / Real.log x := by
  rw [exact_tail_identity hP hx]
  calc
    _ ≤ |(pi x - Li2 x) / x| + |∫ t in Set.Ioi x, (pi t - Li2 t) / t^2| := abs_sub _ _
    _ ≤ C * x ^ (-(1:ℝ)/8) / Real.log x +
        8 * C * x ^ (-(1:ℝ)/8) / Real.log x :=
      add_le_add (endpoint_error_bound hP hx) (actual_tail_bound hP hx)
    _ = _ := by ring

theorem sharper_whole_ray_error (hP : PrimeCountingInput) {x : ℝ}
    (hx : Real.exp 300 ≤ x) :
    |primeReciprocal x - Real.log (Real.log x) - reciprocalConstant| ≤
      C * (x ^ (-(1:ℝ)/8) / Real.log x +
        ∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log t) := by
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 300)) hx
  have hi : |∫ t in Set.Ioi x, (pi t - Li2 t) / t^2| ≤
      C * (∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log t) := by
    calc
      _ ≤ ∫ t in Set.Ioi x, |(pi t - Li2 t) / t^2| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioi x, C * (t ^ (-(9:ℝ)/8) / Real.log t) := by
        apply integral_mono_ae (actual_error_integrable hP hx).abs
          ((log_tail_integrable hx1).const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact input_weight_bound hP (by have htx : x < t := ht; linarith)
      _ = _ := integral_const_mul _ _
  rw [exact_tail_identity hP hx]
  calc
    _ ≤ |(pi x - Li2 x) / x| + |∫ t in Set.Ioi x, (pi t - Li2 t) / t^2| := abs_sub _ _
    _ ≤ C * x ^ (-(1:ℝ)/8) / Real.log x +
        C * (∫ t in Set.Ioi x, t ^ (-(9:ℝ)/8) / Real.log t) :=
      add_le_add (endpoint_error_bound hP hx) hi
    _ = _ := by ring

open Filter
open scoped Topology

theorem prime_reciprocal_tendsto (hP : PrimeCountingInput) :
    Tendsto (fun x : ℝ => primeReciprocal x - Real.log (Real.log x)) atTop
      (𝓝 reciprocalConstant) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-(1:ℝ)/8)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)
  have hl : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hb : Tendsto (fun x : ℝ => 9 * C * x ^ (-(1:ℝ)/8) / Real.log x)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds.mul hp).mul hl)
  have he : Tendsto (fun x : ℝ =>
      primeReciprocal x - Real.log (Real.log x) - reciprocalConstant) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hb
    filter_upwards [eventually_ge_atTop (Real.exp 300)] with x hx
    simpa only [Real.norm_eq_abs] using whole_ray_error hP hx
  simpa only [sub_add_cancel, zero_add] using he.add_const reciprocalConstant

/-- Final consumer: the sole premise is the stated prime-counting input. -/
theorem final_consumer (hP : PrimeCountingInput) :
    ∃ B : ℝ,
      Tendsto (fun x : ℝ => primeReciprocal x - Real.log (Real.log x)) atTop (𝓝 B) ∧
      ∀ x : ℝ, Real.exp 300 ≤ x →
        |primeReciprocal x - Real.log (Real.log x) - B| ≤
          9 * C * x ^ (-(1:ℝ)/8) / Real.log x :=
  ⟨reciprocalConstant, prime_reciprocal_tendsto hP, fun _ hx => whole_ray_error hP hx⟩

theorem unique_reciprocal_limit (hP : PrimeCountingInput) {B : ℝ}
    (hB : Tendsto (fun x : ℝ => primeReciprocal x - Real.log (Real.log x))
      atTop (𝓝 B)) : B = reciprocalConstant :=
  tendsto_nhds_unique hB (prime_reciprocal_tendsto hP)

end ExposureTask
