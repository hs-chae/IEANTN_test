import BoxZeroKernel
import OcticDerivativeMoments

/-! Sharp derivative transport with a genuine complete analytic tail.
The split height remains a free real parameter; it is not a zero truncation. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHOcticPush.BPTSpecialization RHOcticPush.DerivativeMoments
set_option maxHeartbeats 0

noncomputable def derivativeCost (δ t : ℝ) : ℝ :=
  δ * |D (δ*t)| / t * log t

lemma derivativeCost_nonneg {δ t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) :
    0 ≤ derivativeCost δ t := by
  unfold derivativeCost
  have hl := Real.log_nonneg ht
  have ht0 : 0<t := by linarith
  exact mul_nonneg (div_nonneg (mul_nonneg hδ.le (abs_nonneg _)) ht0.le) hl

lemma derivativeCost_tail {δ t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) :
    derivativeCost δ t ≤ 2 * (log t/t^2) := by
  have ht0 : 0<t := by linarith
  have hd := mul_le_mul_of_nonneg_left (D_far (mul_pos hδ ht0)) hδ.le
  have he : δ * (2/(δ*t)) / t = 2/t^2 := by field_simp
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd ht0.le) (Real.log_nonneg ht)
  rw [he] at hh
  simpa [derivativeCost,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

lemma derivativeCost_small {δ t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) :
    derivativeCost δ t ≤ δ^2/3 * log t := by
  have ht0 : 0<t := by linarith
  have hd := D_small (δ*t)
  rw [abs_of_pos (mul_pos hδ ht0)] at hd
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hδ.le) ht0.le)
      (Real.log_nonneg ht)
  have he : δ * (δ*t/3) / t = δ^2/3 := by field_simp <;> ring
  rw [he] at hh
  exact hh

lemma derivativeCost_integrable {δ a : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a) :
    IntegrableOn (derivativeCost δ) (Ioi a) := by
  have hm := (log_sq_integrable ha).const_mul 2
  have hc : ContinuousOn (derivativeCost δ) (Ioi a) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.out]
    unfold derivativeCost
    have hd : ContinuousAt (fun v : ℝ => |D (δ*v)|) t :=
      (D_continuous.comp (continuous_const.mul continuous_id)).abs.continuousAt
    exact (((hd.const_mul δ).div continuousAt_id ht0).mul
      (Real.continuousAt_log ht0)).continuousWithinAt
  apply hm.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (derivativeCost_nonneg hδ (ha.trans ht.le))]
  exact derivativeCost_tail hδ (ha.trans ht.le)

lemma derivativeCost_integral {δ T : ℝ} (hδ : 0 < δ) (hT : 12 ≤ T) :
    (∫ t in Ioi 12, derivativeCost δ t) ≤
      δ^2/3*T*log T + 2*(log T+1)/T := by
  have hT0 : 0<T := by linarith
  have hi := derivativeCost_integrable hδ (a := 12) (by norm_num)
  have hlo : (∫ t in Ioc (12:ℝ) T, derivativeCost δ t) ≤ δ^2/3*T*log T := by
    have hh : (∫ t in Ioc (12:ℝ) T, derivativeCost δ t) ≤
        ∫ t in Ioc (12:ℝ) T, δ^2/3*log T := by
      apply integral_mono_ae (hi.mono_set Ioc_subset_Ioi_self) (integrableOn_const (by simp))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have h1 : 1≤t := by linarith [ht.1]
      exact (derivativeCost_small hδ h1).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) ht.2) (by positivity))
    have he : (∫ t in Ioc (12:ℝ) T, δ^2/3*log T) =
        (T-12)*(δ^2/3*log T) := by
      rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    rw [he] at hh
    have hl : 0 ≤ log T := Real.log_nonneg (by linarith)
    nlinarith [mul_nonneg (sq_nonneg δ) hl]
  have hhi : (∫ t in Ioi T, derivativeCost δ t) ≤ 2*(log T+1)/T := by
    have hT1 : 1≤T := by linarith
    have hh : (∫ t in Ioi T, derivativeCost δ t) ≤
        ∫ t in Ioi T, 2*(log t/t^2) := by
      apply integral_mono_ae (hi.mono_set (Ioi_subset_Ioi hT))
        ((log_sq_integrable hT1).const_mul 2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact derivativeCost_tail hδ (hT1.trans ht.le)
    rw [integral_const_mul,log_sq_integral hT1] at hh
    convert hh using 1 <;> ring
  have he : (∫ t in Ioi 12, derivativeCost δ t) =
      (∫ t in Ioc (12:ℝ) T, derivativeCost δ t) +
        ∫ t in Ioi T, derivativeCost δ t := by
    rw [← Ioc_union_Ioi_eq_Ioi hT]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hT))
  rw [he]
  exact add_le_add hlo hhi

/-- Complete derivative integral with its sharp baseline coefficient1/t²,
plus a rigorously controlled entire derivative correction. -/
theorem kernelDerivative_integral {δ T : ℝ} (hδ : 0 < δ) (hT : 12 ≤ T) :
    (∫ t in Ioi 12, |kernelDerivative δ t| * log t) ≤
      (log 12+1)/12 + δ^2/3*T*log T + 2*(log T+1)/T := by
  have hi := integrable_abs_mul_log_of_decay (a := 12) (K := 3) (by norm_num)
    ((kernelDerivative_continuousOn δ (a := 12) (by norm_num)).mono Ioi_subset_Ici_self)
    (fun t ht => kernelDerivative_decay hδ (by linarith [ht.out]))
  have hm := (log_sq_integrable (a := 12) (by norm_num)).add
    (derivativeCost_integrable hδ (a := 12) (by norm_num))
  have hh : (∫ t in Ioi 12, |kernelDerivative δ t| * log t) ≤
      ∫ t in Ioi 12, log t/t^2 + derivativeCost δ t := by
    apply integral_mono_ae hi hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := by linarith [ht.out]
    have hs := kernelDerivative_sharp (δ := δ) ht0
    rw [abs_of_pos hδ] at hs
    have hu := mul_le_mul_of_nonneg_right hs (Real.log_nonneg (show (1:ℝ) ≤ t by linarith [ht.out]))
    convert hu using 1 <;> dsimp [derivativeCost] <;> ring
  rw [integral_add (log_sq_integrable (a := 12) (by norm_num))
    (derivativeCost_integrable hδ (a := 12) (by norm_num)),
    log_sq_integral (by norm_num)] at hh
  linarith [derivativeCost_integral hδ hT]

#print axioms derivativeCost_integral
#print axioms kernelDerivative_integral
end RHOcticPush.BoxZero
