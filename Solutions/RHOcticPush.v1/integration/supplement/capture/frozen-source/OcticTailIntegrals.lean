import OcticTail
namespace RHOcticPush.Moments
open Real Set MeasureTheory Filter
set_option maxHeartbeats 0
lemma inverse_square_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => 1/y^2) (Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hT
  apply h.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp only
  rw [Real.rpow_neg (by linarith [hy.out] : 0 ≤ y), Real.rpow_ofNat]
  simp [one_div]
lemma inverse_square_integral {T : ℝ} (hT : 0 < T) :
    (∫ y : ℝ in Ioi T, 1/y^2) = 1/T := by
  have he : (∫ y : ℝ in Ioi T, 1/y^2) = ∫ y : ℝ in Ioi T, y^(-2 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [Real.rpow_neg (by linarith [hy.out] : 0 ≤ y), Real.rpow_ofNat]
    simp [one_div]
  rw [he, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
  norm_num [Real.rpow_neg_one, one_div]
lemma transform_abs_continuous : Continuous (fun y => |EvenKernel.transform 4 y|) :=
  (continuous_iff_continuousAt.mpr fun y =>
    (DerivativeBounds.transform_hasDerivAt y).continuousAt).abs

theorem octic_abs_tail_integrable :
    IntegrableOn (fun y => |EvenKernel.transform 4 y|) (Ioi 1000) := by
  have hm := (inverse_square_integrable (by norm_num : (0 : ℝ) < 1000)).const_mul
    (16113/1000 : ℝ)
  apply hm.mono' (transform_abs_continuous.aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change abs (abs (EvenKernel.transform 4 y)) ≤ _
  rw [abs_abs]
  exact (octic_tail_bound hy.le).trans_eq (by ring)

theorem octic_abs_tail :
    (∫ y in Ioi (1000 : ℝ), |EvenKernel.transform 4 y|) ≤ 16113/1000000 := by
  calc
    _ ≤ ∫ y in Ioi (1000 : ℝ), (16113/1000)*(1/y^2) := by
      apply integral_mono_ae octic_abs_tail_integrable
        ((inverse_square_integrable (by norm_num : (0 : ℝ) < 1000)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (octic_tail_bound hy.le).trans_eq (by ring)
    _ = _ := by
      rw [integral_const_mul, inverse_square_integral (by norm_num)]
      norm_num

theorem octic_log_tail_integrable :
    IntegrableOn (fun y => |EvenKernel.transform 4 y| *log y) (Ioi 1000) := by
  exact BPTSpecialization.integrable_abs_mul_log_of_decay (by norm_num)
    (continuous_iff_continuousAt.mpr fun y =>
      (DerivativeBounds.transform_hasDerivAt y).continuousAt).continuousOn
    (fun y hy => octic_tail_bound hy.le)

theorem octic_log_tail :
    (∫ y in Ioi (1000 : ℝ), |EvenKernel.transform 4 y| *log y) ≤
      (16113/1000000)*(log 1000+1) := by
  calc
    _ ≤ ∫ y in Ioi (1000 : ℝ), (16113/1000)*(log y/y^2) := by
      apply integral_mono_ae octic_log_tail_integrable
        ((BPTSpecialization.log_sq_integrable (by norm_num : (1 : ℝ) ≤ 1000)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have h := mul_le_mul_of_nonneg_right (octic_tail_bound hy.le)
        (log_nonneg (by linarith [hy.out] : 1 ≤ y))
      exact h.trans_eq (by ring)
    _ = _ := by rw [integral_const_mul, log_tail_integral (by norm_num)]; ring
#print axioms octic_abs_tail
#print axioms octic_log_tail
end RHOcticPush.Moments
