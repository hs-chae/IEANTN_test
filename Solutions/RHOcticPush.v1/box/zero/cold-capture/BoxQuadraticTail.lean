import BoxEndpointInfinite
import OcticDerivativeMoments

/-! A genuine complete quadratic reciprocal-zero tail from BPT. This is used
above a fixed transport height; no finite zero certificate replaces the tail. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
open RHOcticPush.BPTSpecialization RHOcticPush.DerivativeMoments
set_option maxHeartbeats 0

lemma reciprocal_square_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1/t^2) (-2/t^3) t := by
  apply ((hasDerivAt_const t (1:ℝ)).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero 2 ht.ne')).congr_deriv
  dsimp
  field_simp <;> ring

lemma quadratic_density_integral {a : ℝ} (ha : 2*Real.pi ≤ a) :
    (∫ t in Ioi a, (1/t^2)*density t) =
      (log (a/(2*Real.pi))+1)/(2*Real.pi*a) := by
  have ha1 : 1 ≤ a := by linarith [Real.pi_gt_three]
  have ha0 : 0 < a := by linarith
  have he : (∫ t in Ioi a, (1/t^2)*density t) =
      (1/(2*Real.pi))*((∫ t in Ioi a, log t/t^2) -
        log (2*Real.pi)*(∫ t in Ioi a, 1/t^2)) := by
    calc
      _ = ∫ t in Ioi a, (1/(2*Real.pi)) *
          (log t/t^2 - log (2*Real.pi)*(1/t^2)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        unfold density
        rw [Real.log_div (by linarith [ht.out] : t ≠ 0) (by positivity)]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_sub (log_sq_integrable ha1)
          ((inv_sq_integrable ha0).const_mul _), integral_const_mul]
  rw [he, log_sq_integral ha1, inv_sq_integral ha0,
    Real.log_div ha0.ne' (by positivity)]
  field_simp <;> ring

lemma quadratic_derivative_decay {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    |-2/t^3| ≤ (2/a)/t^2 := by
  have ht0 : 0 < t := ha.trans_le ht
  rw [abs_div, abs_of_neg (by norm_num : (-2:ℝ)<0),
    abs_of_pos (pow_pos ht0 3)]
  calc
    _ = (2/t^2)*(1/t) := by ring
    _ ≤ (2/t^2)*(1/a) := mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le ha ht) (by positivity)
    _ = _ := by ring

lemma quadratic_derivative_log_integrable {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => |-2/t^3| * log t) (Ioi a) := by
  apply integrable_abs_mul_log_of_decay ha
    (f := fun t : ℝ => -2/t^3) (K := 2/a)
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.out]
    fun_prop (disch := positivity)
  · intro t ht
    exact quadratic_derivative_decay (by linarith) ht.le

lemma quadratic_derivative_log_bound {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Ioi a, |-2/t^3| * log t) ≤ 2*(log a+1)/a^2 := by
  have ha0 : 0<a := by linarith
  have hm := (log_sq_integrable ha).const_mul (2/a)
  have hi := quadratic_derivative_log_integrable ha
  have hle : (∫ t in Ioi a, |-2/t^3| * log t) ≤
      ∫ t in Ioi a, (2/a)*(log t/t^2) := by
    apply integral_mono_ae hi hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := by linarith [ht.out]
    have hdiv : |-2/t^3| ≤ (2/a)/t^2 := quadratic_derivative_decay ha0 ht.le
    have hh := mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (ha.trans ht.le))
    convert hh using 1 <;> ring
  rw [integral_const_mul, log_sq_integral ha] at hle
  convert hle using 1 <;> field_simp <;> ring

/-- Complete positive-zero tail; multiplicities and all heights above a are included. -/
theorem quadratic_tail_bound (h : PublishedBound) {a : ℝ} (ha : 2*Real.pi ≤ a) :
    Summable (fun z : PositiveZero a => (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : PositiveZero a, (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ)) ≤
      (log (a/(2*Real.pi))+1)/(2*Real.pi*a) +
        (7/25)*(3*log a+2)/a^2 := by
  have ha1 : 1≤a := by linarith [Real.pi_gt_three]
  have ha0 : 0<a := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1/t^2) (Ioi a) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.out]
    fun_prop (disch := positivity)
  have hd : ContinuousOn (fun t : ℝ => -2/t^3) (Ici a) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.out]
    fun_prop (disch := positivity)
  have haabs (t : ℝ) : |1/t^2| = 1/t^2 := abs_of_nonneg (by positivity)
  have hi : IntegrableOn (fun t : ℝ => |1/t^2| * density t) (Ioi a) := by
    apply density_integrable ha hc
    convert log_sq_integrable ha1 using 1
    ext t
    rw [haabs]
    ring
  have hb : Tendsto (fun t : ℝ => |1/t^2| * log t) atTop (nhds 0) := by
    convert log_sq_tends_zero using 1
    ext t
    rw [haabs]
    ring
  have hh := RHOcticPush.BPTInfinite.infinite_absolute_bound h ha
    (fun t ht => reciprocal_square_derivative (ha0.trans_le ht)) hd hi
      (quadratic_derivative_log_integrable ha1) hb
  have he : (fun z : PositiveZero a => |1/z.val.im^2| * (IEANTN.zetaOrder z.val : ℝ)) =
      (fun z : PositiveZero a => (1/z.val.im^2)*(IEANTN.zetaOrder z.val : ℝ)) := by
    funext z
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤1/z.val.im^2)]
  rw [he] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hem : (∫ t in Ioi a, |1/t^2| * density t) =
      (∫ t in Ioi a, (1/t^2)*density t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change |1/t^2| * density t = (1/t^2)*density t
    rw [haabs]
  rw [hem,quadratic_density_integral ha,
    abs_of_nonneg (by positivity : (0:ℝ)≤1/a^2)]
  have hd' := quadratic_derivative_log_bound ha1
  calc
    _ ≤ (log (a/(2*Real.pi))+1)/(2*Real.pi*a) +
        (7/25)*((1/a^2)*log a + 2*(log a+1)/a^2) := by gcongr
    _ = _ := by ring

#print axioms quadratic_density_integral
#print axioms quadratic_derivative_log_bound
#print axioms quadratic_tail_bound
end RHOcticPush.BoxZero
