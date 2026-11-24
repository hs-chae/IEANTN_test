import BoxScaledMoments
import BoxDerivativeTransport

/-! Complete actual unshifted positive-zero bound; every infinite integral and
moment transport is discharged. Actual complex source-packet shift is separate. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

lemma kernel_boundary {d : ℝ} : |kernel d 12| ≤ 1/12 := by
  rw [kernel,abs_div,abs_of_pos (by norm_num : (0:ℝ)<12)]
  exact div_le_div_of_nonneg_right (F_abs _) (by norm_num)

/-- Genuine whole infinite positive-zero family, with multiplicities. -/
theorem unshifted_positive_bound (h : PublishedBound) {d : ℝ} (hd : 0<d)
    (hsmall : 12*d≤1) :
    2*(∑' z : PositiveZero 12,|kernel d z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      mainMoment d + endpointAllowance + derivativeAllowance d + 4*d^2 := by
  have hz := kernel_infinite_bound h hd
  have hm := box_scaled_density_bound hd hsmall
  have hder := kernelDerivative_integral hd (by norm_num : (12:ℝ)≤32768)
  have he : ZeroCount.v1.rvmMain 12 = mainCount 12 := rfl
  have hb : 2*|kernel d 12| * |ZeroCount.v1.rvmMain 12| ≤ 2*mainCount 12/12 := by
    rw [he,abs_of_nonneg mainCount_twelve_nonneg]
    have hh := mul_le_mul_of_nonneg_right (kernel_boundary (d := d)) mainCount_twelve_nonneg
    linarith
  unfold endpointAllowance derivativeAllowance
  nlinarith [hz.2]

#print axioms unshifted_positive_bound
end RHOcticPush.BoxZero
