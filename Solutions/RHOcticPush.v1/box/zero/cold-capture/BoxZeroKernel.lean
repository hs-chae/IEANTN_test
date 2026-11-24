import BoxEndpointInfinite
import OcticBPTSpecialization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import PsiSmoothing
import IEANTN.Vocabulary.RHSmoothing

/-! Actual Box Fourier kernel and the full infinite positive-zero sum.
Both small and large derivative bounds are proved for every real argument in
use; no numerical grid or imported moment estimate is assumed. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open scoped Topology
open RHLimit.BPTZeroCount RHOcticPush.BPTSpecialization
open RHOcticPush.DerivativeBounds RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

noncomputable def F (y : ℝ) : ℝ :=
  IEANTN.RHSmoothing.fourier IEANTN.RHSmoothing.box y
noncomputable def D (y : ℝ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, -((1 / 2 : ℝ) * u) * sin (y * u)

lemma F_derivative (y : ℝ) : HasDerivAt F (D y) y :=
  cosine_integral_derivative (fun _ : ℝ => (1 / 2 : ℝ)) continuous_const y

lemma D_continuous : Continuous D := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (sine_integral_derivative (fun u : ℝ => -((1 / 2 : ℝ) * u))
    (by fun_prop) y).continuousAt

lemma F_eq {y : ℝ} (hy : y ≠ 0) : F y = sin y / y :=
  PsiSmoothing.box_fourier hy

lemma F_sinc (y : ℝ) : F y = Real.sinc y := by
  by_cases hy : y = 0
  · subst y
    norm_num [F, IEANTN.RHSmoothing.fourier, IEANTN.RHSmoothing.box]
  · rw [F_eq hy, Real.sinc_of_ne_zero hy]

lemma F_abs (y : ℝ) : |F y| ≤ 1 := by
  rw [F_sinc]
  exact Real.abs_sinc_le_one y

lemma F_decay {y : ℝ} (hy : 0 < y) : |F y| ≤ 1 / y := by
  rw [F_eq hy.ne', abs_div, abs_of_pos hy]
  exact div_le_div_of_nonneg_right (abs_sin_le_one y) hy.le

lemma D_small (y : ℝ) : |D y| ≤ |y| / 3 := by
  have hc : Continuous (fun u : ℝ => -((1 / 2 : ℝ) * u) * sin (y * u)) := by
    fun_prop
  have hm : Continuous (fun u : ℝ => |y| / 2 * u ^ 2) := by fun_prop
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |-((1 / 2 : ℝ) * u) * sin (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, |y| / 2 * u ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.abs.intervalIntegrable _ _) (hm.intervalIntegrable _ _)
      intro u _
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      have hs := Real.abs_sin_le_abs (x := y*u)
      rw [abs_mul] at hs
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1/2:ℝ)*|u| by positivity)
      calc
        _ ≤ (1/2:ℝ) * |u| * (|y| * |u|) := hh
        _ = _ := by ring_nf; rw [sq_abs]; ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring

lemma D_eq {y : ℝ} (hy : y ≠ 0) : D y = (y * cos y - sin y) / y ^ 2 := by
  have h : HasDerivAt (fun y : ℝ => sin y / y)
      ((cos y * y - sin y * 1) / y ^ 2) y :=
    (Real.hasDerivAt_sin y).div (hasDerivAt_id y) hy
  have he : F =ᶠ[𝓝 y] (fun y : ℝ => sin y / y) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    exact F_eq ht
  have hu := (F_derivative y).congr_of_eventuallyEq he.symm
  have hh := hu.unique h
  simpa only [mul_one, one_mul, mul_comm] using hh

lemma D_far {y : ℝ} (hy : 0 < y) : |D y| ≤ 2 / y := by
  by_cases hy1 : y ≤ 1
  · have h := D_small y
    rw [abs_of_pos hy] at h
    apply h.trans
    apply (le_div_iff₀ hy).mpr
    nlinarith
  · have hy1' : 1 ≤ y := le_of_not_ge hy1
    rw [D_eq hy.ne', abs_div, abs_of_nonneg (sq_nonneg y)]
    apply (div_le_iff₀ (sq_pos_of_pos hy)).mpr
    have ha := abs_sub (y * cos y) (sin y)
    rw [abs_mul, abs_of_pos hy] at ha
    have hb := mul_le_mul_of_nonneg_left (abs_cos_le_one y) hy.le
    have hs := abs_sin_le_one y
    have he : (2 / y) * y ^ 2 = 2 * y := by field_simp <;> ring
    rw [he]
    linarith

noncomputable def kernel (δ t : ℝ) : ℝ := F (δ * t) / t
noncomputable def kernelDerivative (δ t : ℝ) : ℝ :=
  δ * D (δ * t) / t - F (δ * t) / t ^ 2

lemma kernel_derivative {δ t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernel δ) (kernelDerivative δ t) t := by
  have h := ((F_derivative (δ * t)).comp t ((hasDerivAt_id t).const_mul δ)).div
    (hasDerivAt_id t) ht.ne'
  apply h.congr_deriv
  dsimp [kernelDerivative]
  field_simp <;> ring

lemma kernelDerivative_continuousOn (δ : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (kernelDerivative δ) (Ici a) := by
  intro t ht
  have ht0 : t ≠ 0 := (ha.trans_le ht).ne'
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (F_derivative y).continuousAt)
  unfold kernelDerivative
  exact (((continuous_const.mul (D_continuous.comp (continuous_const.mul continuous_id))).continuousAt.div
    continuousAt_id ht0).sub
      ((hF.comp (continuous_const.mul continuous_id)).continuousAt.div
        (continuousAt_id.pow 2) (pow_ne_zero 2 ht0))).continuousWithinAt

lemma kernel_decay {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    |kernel δ t| ≤ (1 / δ) / t ^ 2 := by
  rw [kernel, abs_div, abs_of_pos ht]
  have h := div_le_div_of_nonneg_right (F_decay (mul_pos hδ ht)) ht.le
  calc
    _ ≤ (1/(δ*t))/t := h
    _ = _ := by field_simp <;> ring

lemma kernelDerivative_sharp {δ t : ℝ} (ht : 0 < t) :
    |kernelDerivative δ t| ≤ 1 / t ^ 2 + |δ| * |D (δ * t)| / t := by
  unfold kernelDerivative
  calc
    _ ≤ |δ * D (δ*t)/t| + |F (δ*t)/t^2| := abs_sub _ _
    _ ≤ |δ| * |D (δ*t)| / t + 1 / t^2 := by
      rw [abs_div, abs_mul, abs_of_pos ht, abs_div,
        abs_of_nonneg (sq_nonneg t)]
      gcongr
      exact F_abs _
    _ = _ := by ring

lemma kernelDerivative_decay {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    |kernelDerivative δ t| ≤ 3 / t ^ 2 := by
  have hh := kernelDerivative_sharp (δ := δ) ht
  rw [abs_of_pos hδ] at hh
  have hd := mul_le_mul_of_nonneg_left (D_far (mul_pos hδ ht)) hδ.le
  have ht' := div_le_div_of_nonneg_right hd ht.le
  have he : 1/t^2 + (δ*(2/(δ*t)))/t = 3/t^2 := by field_simp <;> ring
  linarith

/-- Full infinite actual Box kernel bound. Analytic side conditions are all
proved; the only remaining input is the independently published zero-count bound. -/
theorem kernel_infinite_bound (h : PublishedBound) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun z : PositiveZero 12 => |kernel δ z.val.im| *
      (IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : PositiveZero 12, |kernel δ z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      (∫ t in Ioi 12, |kernel δ t| * density t) +
      (7 / 25) * (∫ t in Ioi 12, |kernelDerivative δ t| * log t) +
        |kernel δ 12| * |ZeroCount.v1.rvmMain 12| := by
  have hc : ContinuousOn (kernel δ) (Ioi 12) := by
    intro t ht
    exact (kernel_derivative (by linarith [ht.out])).continuousAt.continuousWithinAt
  have hd : ContinuousOn (kernelDerivative δ) (Ici 12) :=
    kernelDerivative_continuousOn δ (by norm_num)
  apply infinite_absolute_twelve h (fun t ht => kernel_derivative (by linarith [ht.out])) hd
  · apply density_integrable (by linarith [Real.pi_lt_four]) hc
    exact integrable_abs_mul_log_of_decay (by norm_num) hc
      (fun t ht => kernel_decay hδ (by linarith [ht.out]))
  · exact integrable_abs_mul_log_of_decay (by norm_num)
      (hd.mono Ioi_subset_Ici_self) (fun t ht => kernelDerivative_decay hδ (by linarith [ht.out]))
  · apply abs_mul_log_tends_zero_of_decay
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact kernel_decay hδ ht

#print axioms F_derivative
#print axioms D_small
#print axioms D_far
#print axioms kernel_infinite_bound
end RHOcticPush.BoxZero
