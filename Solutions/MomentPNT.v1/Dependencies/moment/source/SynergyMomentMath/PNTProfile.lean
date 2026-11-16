/- Every new numerical provider is consumed, shared by source-first and N+ paths. -/
import SynergyMomentMath.PNT300
namespace SynergyMomentMath.PNTProfile
open SynergyAnalytic SynergyAnalytic.HeightPoint
open IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
noncomputable section

theorem future_from_moments
 (mass : totalMass SynergyMomentMath.Real.mass 768 ≤ PNT300.massUpper)
 (moment : firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768 ≤ PNT300.momentUpper)
 {L : ℝ} (future : 330 ≤ L)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ
  (finitePNTCoefficient (momentEnvelope PNT300.massUpper PNT300.momentUpper L) L)
  0 (7/8) (_root_.Real.exp L) := by
 have finite:=finiteCoefficient_moment_bound Bounds.mass_nonnegative Bounds.d_range
  mass moment (by linarith : 300 ≤ L)
 exact pi_ray_of_finite heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
  future finite (PointCaps.actual_caps SourceMomentSumsV1.Real.domains h hRH)
  h hCHJ hrvm hsmall hlow hRH hQRH

theorem point_from_moments
 (mass : totalMass SynergyMomentMath.Real.mass 768 ≤ PNT300.massUpper)
 (moment : firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768 ≤ PNT300.momentUpper)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : _root_.Real.exp 330 ≤ x) :
 Eπ x ≤ finitePNTCoefficient
  (momentEnvelope PNT300.massUpper PNT300.momentUpper (_root_.Real.log x))
  (_root_.Real.log x)*x^(-(1:ℝ)/8) := by
 have positive : 0 < x:=(_root_.Real.exp_pos 330).trans_le hx
 have future : 330 ≤ _root_.Real.log x := by
  have q:=_root_.Real.log_le_log (_root_.Real.exp_pos 330) hx
  simpa only [_root_.Real.log_exp] using q
 have ray:=future_from_moments mass moment future h hCHJ hrvm hsmall hlow hRH hQRH
 have value:=ray x (by rw [_root_.Real.exp_log positive])
 simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using value
#print axioms future_from_moments
#print axioms point_from_moments
end
end SynergyMomentMath.PNTProfile
