import BoxScaledMoments
import BoxSecondMoment
import BoxImproved
import FiniteApplicability

/-! The actual main moment and the entire small-hole remainder are bounded. -/
namespace RHOcticPush.BoxZero
open Real Set IEANTN.RHSmoothing
set_option maxHeartbeats 0

theorem mainMoment_actual_bound {L : ℝ} (hL : 35 ≤ L) :
    mainMoment (delta L) ≤ L^2 := by
  have h0 : 0 < L := by linarith
  have hv0 : 0 ≤ v L := by
    unfold v
    linarith [RHOcticPush.Applicability.log_le_half h0]
  have hv : v L ≤ L/2 := by
    unfold v
    have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)
    linarith
  have hs : (v L)^2 ≤ L^2/4 := by nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hm : 2 * Real.log 2 * v L ≤ L := by nlinarith
  have hj := RHOcticPush.BoxTail.source_moment_improved_closed
    RHOcticPush.BoxGamma.second_moment_identity
  change J box 1 < 70871/100000 at hj
  unfold mainMoment
  rw [actual_delta_scale h0, RHOcticPush.BoxGamma.actual_box_J0]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr Real.pi_gt_three.le)]

theorem uniform_zero_residual_with_lowHole {L : ℝ} (hL : 35 ≤ L) :
    Real.exp (delta L) *
        (endpointAllowance + derivativeAllowance (delta L) + shiftAllowance (delta L) +
          4 * (delta L)^2) + 2 * delta L * L^2 < (131/1000 : ℝ) := by
  have hd := delta_small hL
  have hd0 := hd.1.le
  have hsq := delta_square_budget hL
  have hlog : 0 ≤ Real.log 32768 := Real.log_nonneg (by norm_num)
  have hder : 0 ≤ derivativeAllowance (delta L) := by unfold derivativeAllowance; positivity
  have hshift : 0 ≤ shiftAllowance (delta L) := by unfold shiftAllowance; positivity
  have hpoly : endpointAllowance + derivativeAllowance (delta L) + shiftAllowance (delta L) +
      4 * (delta L)^2 ≤ (259/2000 : ℝ) + derivativeAllowance (1/7000000) +
        shiftAllowance (1/7000000) + 4 * (1/7000000 : ℝ)^2 := by
    have hb := endpointAllowance_lt.le
    unfold derivativeAllowance shiftAllowance
    gcongr <;> first | exact hd0 | exact hd.2.le
  calc
    _ ≤ Real.exp (1/7000000 : ℝ) *
        ((259/2000 : ℝ) + derivativeAllowance (1/7000000) + shiftAllowance (1/7000000) +
          4 * (1/7000000 : ℝ)^2) + (1/2900 : ℝ) := by
      have hp : 0 ≤ endpointAllowance + derivativeAllowance (delta L) + shiftAllowance (delta L) +
          4 * (delta L)^2 := by
        exact add_nonneg (add_nonneg (add_nonneg endpointAllowance_nonneg hder) hshift)
          (by positivity)
      have he := mul_le_mul (Real.exp_le_exp.mpr hd.2.le) hpoly hp (by positivity)
      linarith
    _ < _ := by
      unfold derivativeAllowance shiftAllowance
      interval_decide 90 (trust := kernel) <;> ring

#print axioms mainMoment_actual_bound
#print axioms uniform_zero_residual_with_lowHole
end RHOcticPush.BoxZero
