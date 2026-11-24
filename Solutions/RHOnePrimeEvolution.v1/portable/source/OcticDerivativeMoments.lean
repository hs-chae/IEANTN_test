import OcticBPTSpecialization

/-! Exact full derivative moments used by the sharp BPT residual.
The split is at4; all tails are analytic improper integrals, with no cutoff premise. -/
namespace RHOcticPush.DerivativeMoments
open Real Set MeasureTheory
open RHOcticPush.DerivativeBounds RHOcticPush.BPTSpecialization
set_option maxHeartbeats 0

lemma inv_sq_derivative {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => (-1 : ℝ) / t) (1 / t ^ 2) t := by
  apply ((hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id t) ht).congr_deriv
  simp

lemma inv_sq_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => (-1 : ℝ) / t) (l := 0)
  · intro t ht
    exact inv_sq_derivative (ne_of_gt (ha.trans_le ht))
  · intro t _
    positivity
  · simpa only [neg_div, one_div, neg_zero] using
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0)).neg

lemma inv_sq_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, 1 / t ^ 2) = 1 / a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => (-1 : ℝ) / t) (f' := fun t : ℝ => 1 / t ^ 2)
    (fun t ht => inv_sq_derivative (ne_of_gt (ha.trans_le ht)))
    (inv_sq_integrable ha)
    (by simpa only [neg_div, one_div, neg_zero] using
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0)).neg)
  rw [h]
  ring

lemma log_sq_integral {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Ioi a, log t / t ^ 2) = (log a + 1) / a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => -(log t + 1) / t)
    (f' := fun t : ℝ => log t / t ^ 2)
    (fun t ht => log_inverse_primitive_derivative (by linarith [ht.out]))
    (log_sq_integrable ha) log_inverse_primitive_limit
  rw [h]
  ring

lemma first_continuous : Continuous first :=
  continuous_iff_continuousAt.mpr (fun t => (first_hasDerivAt t).continuousAt)

lemma first_tail_integrable : IntegrableOn (fun t : ℝ => |first t|) (Ioi 4) := by
  apply ((inv_sq_integrable (by norm_num : (0 : ℝ) < 4)).const_mul 34).mono'
    first_continuous.abs.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_abs]
  simpa [div_eq_mul_inv] using first_abs_le_decay (show t ≠ 0 by linarith [ht.out])

lemma first_integrable : IntegrableOn (fun t : ℝ => |first t|) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 4), integrableOn_union]
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    (first_continuous.abs.intervalIntegrable 0 4), first_tail_integrable⟩

lemma first_integral_le : (∫ t in Ioi (0 : ℝ), |first t|) ≤ 117 / 10 := by
  have hs : IntegrableOn (fun t : ℝ => |first t|) (Ioc 0 4) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (first_continuous.abs.intervalIntegrable 0 4)
  have hsplit : (∫ t in Ioi (0 : ℝ), |first t|) =
      (∫ t in Ioc (0 : ℝ) 4, |first t|) + ∫ t in Ioi (4 : ℝ), |first t| := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 4)]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hs first_tail_integrable
  have hlo : (∫ t in Ioc (0 : ℝ) 4, |first t|) ≤ 16 / 5 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      _ ≤ ∫ t in (0 : ℝ)..4, (4 / 5 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (first_continuous.abs.intervalIntegrable 0 4) (intervalIntegrable_const)
          (fun t _ => first_abs_le t)
      _ = 16 / 5 := by norm_num
  have hhi : (∫ t in Ioi (4 : ℝ), |first t|) ≤ 17 / 2 := by
    calc
      _ ≤ ∫ t in Ioi (4 : ℝ), (34 : ℝ) * (1 / t ^ 2) := by
        apply integral_mono_ae first_tail_integrable
          ((inv_sq_integrable (by norm_num : (0 : ℝ) < 4)).const_mul 34)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simpa [div_eq_mul_inv] using first_abs_le_decay (show t ≠ 0 by linarith [ht.out])
      _ = 17 / 2 := by rw [integral_const_mul, inv_sq_integral (by norm_num)]; norm_num
  rw [hsplit]
  linarith

lemma first_log_integrable :
    IntegrableOn (fun t : ℝ => |first t| * log t) (Ioi 1) :=
  integrable_abs_mul_log_of_decay (by norm_num) first_continuous.continuousOn
    (fun t ht => first_abs_le_decay (show t ≠ 0 by linarith [ht.out]))

lemma first_log_integral_lt :
    (∫ t in Ioi (1 : ℝ), |first t| * log t) < 24 := by
  have hlogc : ContinuousOn log (uIcc (1 : ℝ) 4) := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4)]
    intro t ht
    exact (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
  have hs : IntegrableOn (fun t : ℝ => |first t| * log t) (Ioc 1 4) :=
    first_log_integrable.mono_set Ioc_subset_Ioi_self
  have ht : IntegrableOn (fun t : ℝ => |first t| * log t) (Ioi 4) :=
    first_log_integrable.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit : (∫ t in Ioi (1 : ℝ), |first t| * log t) =
      (∫ t in Ioc (1 : ℝ) 4, |first t| * log t) +
        ∫ t in Ioi (4 : ℝ), |first t| * log t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 4)]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hs ht
  have hlo : (∫ t in Ioc (1 : ℝ) 4, |first t| * log t) ≤
      (4 / 5) * (4 * log 4 - 3) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
    calc
      _ ≤ ∫ t in (1 : ℝ)..4, (4 / 5 : ℝ) * log t := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hs)
          ((hlogc.const_mul (4 / 5)).intervalIntegrable)
        intro t ht
        exact mul_le_mul_of_nonneg_right (first_abs_le t) (log_nonneg ht.1)
      _ = (4 / 5) * (4 * log 4 - 3) := by
        rw [intervalIntegral.integral_const_mul, integral_log]
        norm_num
        ring
  have hhi : (∫ t in Ioi (4 : ℝ), |first t| * log t) ≤
      (17 / 2) * (log 4 + 1) := by
    calc
      _ ≤ ∫ t in Ioi (4 : ℝ), (34 : ℝ) * (log t / t ^ 2) := by
        apply integral_mono_ae ht ((log_sq_integrable (by norm_num : (1 : ℝ) ≤ 4)).const_mul 34)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          |first t| * log t ≤ (34 / t ^ 2) * log t :=
            mul_le_mul_of_nonneg_right (first_abs_le_decay (by linarith [ht.out]))
              (log_nonneg (by linarith [ht.out]))
          _ = _ := by ring
      _ = (17 / 2) * (log 4 + 1) := by
        rw [integral_const_mul, log_sq_integral (by norm_num)]
        ring
  have hlog4 : log (4 : ℝ) < 7 / 5 := by
    have he : log (4 : ℝ) = 2 * log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h
      exact h
    rw [he]
    linarith [Real.log_two_lt_d9]
  rw [hsplit]
  linarith

#print axioms first_integral_le
#print axioms first_log_integral_lt
end RHOcticPush.DerivativeMoments
