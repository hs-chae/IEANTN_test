import SynergyAnalytic.ActualWeightedFinite
import SynergyAnalytic.Smoothing
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerBetaA.ActualObject
set_option maxHeartbeats 0

/-- Numerical residual contract for three UNIVERSAL integrals.  This predicate
must be discharged, not added to the analytic source assumptions. -/
def UniversalBasisCaps (j0 j1 j2 : ℝ) : Prop := ∀ b ≥ 1,
  basisZero b ≤ j0 ∧ basisOne b ≤ j1 ∧ basisTwo b ≤ j2

noncomputable def errorBudget (T h r eps eta m1 m2 j0 j1 j2 : ℝ) : ℝ :=
  (1+eps)*(zetaScale T)^2*(T*Real.log T)*
    ((1+eta)*(m1*(j0+(2/h)*j1+(1/h^2)*j2)+m2*universalPeak)+
      (1+1/eta)*r^2*(m1*gaussianArea+m2))+(1+1/eps)*T*gaussianArea

noncomputable def criticalMassD (T x : ℝ) : ℝ :=
  T*‖mollifiedError T (vertical (1/2) (x*T))‖^2

theorem criticalMassD_continuous (T : ℝ) : Continuous (criticalMassD T) := by
  unfold criticalMassD
  exact ((((critical_error_continuous T).comp (continuous_id.mul_const T)).norm.pow 2).const_mul T)

theorem scaledCriticalF_hasDerivAt (T x : ℝ) :
    HasDerivAt (scaledCriticalF T) (criticalMassD T x) x := by
  have hg := (critical_error_continuous T).norm.pow 2
  have hd := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 (x*T))
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hc := hd.comp x ((hasDerivAt_id x).mul_const T)
  convert hc using 1 <;> first | rfl | simp [scaledCriticalF,cumulativeSquare,criticalMassD,mul_comm]

/-- The complete continuous-height source moment theorem.  There is no new
Shape, infinite-tail, integrability, or desired-moment source assumption.
Only the three explicitly displayed universal numerical residuals remain. -/
theorem actual_source_moment_from_basis
    {T h r eps eta m1 m2 j0 j1 j2 : ℝ}
    (hT : 1 < T) (hh : 14 ≤ h) (hhT : h ≤ Real.log T)
    (hr : (1461/1000:ℝ)/zetaScale T ≤ r) (he : 0 < eps) (ht : 0 < eta)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hcaps : UniversalBasisCaps j0 j1 j2)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 → ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHigh : ∀ u : ℝ, 3 ≤ u → ‖riemannZeta (vertical (1/2) u)‖ ≤
      (611/1000:ℝ)*u^((1:ℝ)/6)*Real.log u)
    (hmean : ∀ t > 0,
      (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
        (m1*t+m2*T)*Real.log T)
    (hsmooth : sourceMoment T (1/2) ≤
      (8*(601/5000:ℝ)*Real.exp ((601/5000:ℝ)/(2*T^2)))*
        (∫ x in Ioi 0, WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x)) :
    sourceMoment T (1/2) ≤ 2*Real.exp ((601/5000:ℝ)/(2*T^2))*
      errorBudget T h r eps eta m1 m2 j0 j1 j2 := by
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hh0 : 0 < h := by linarith
  have hfinite : ∀ b ≥ 1, (∫ x in (0:ℝ)..b, gaussian0 x*criticalMassD T x) ≤
      errorBudget T h r eps eta m1 m2 j0 j1 j2 := by
    intro b hb
    have hr0 := actual_finite_error_three_basis hT hh hhT hb hr he ht hm1 hm2 hLow hHigh hmean
    have hJ := hcaps b hb
    have hC : m1*(basisZero b+(2/h)*basisOne b+(1/h^2)*basisTwo b)+m2*universalPeak ≤
        m1*(j0+(2/h)*j1+(1/h^2)*j2)+m2*universalPeak := by
      gcongr
      · exact hJ.1
      · exact hJ.2.1
      · exact hJ.2.2
    have hm := mul_le_mul_of_nonneg_left hC
      (show 0 ≤ (1+eps)*(zetaScale T)^2*(T*Real.log T)*(1+eta) by positivity)
    have hRaw : (∫ x in (0:ℝ)..b, T*gaussian0 x*‖mollifiedError T (vertical (1/2) (x*T))‖^2) ≤
        errorBudget T h r eps eta m1 m2 j0 j1 j2 := by
      unfold errorBudget
      nlinarith
    convert hRaw using 1
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [criticalMassD]
    ring
  have hF0 : scaledCriticalF T 0 = 0 := by simp [scaledCriticalF,cumulativeSquare]
  have hg := gaussian_cumulative_of_uniform_error (by norm_num : (0:ℝ)<601/2500)
    (scaledCriticalF_continuous T) (criticalMassD_continuous T)
    (fun x => scaledCriticalF_hasDerivAt T x) hF0
    (fun x hx => scaledCriticalF_nonneg hTp.le hx) hfinite
  have heq : (∫ x in Ioi (0:ℝ), x*Real.exp (-(601/2500:ℝ)*x^2)*scaledCriticalF T x) =
      ∫ x in Ioi (0:ℝ), WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x := rfl
  rw [heq] at hg
  have hm := mul_le_mul_of_nonneg_left hg.2
    (show 0 ≤ 2*Real.exp ((601/5000:ℝ)/(2*T^2)) by positivity)
  nlinarith

#print axioms actual_source_moment_from_basis
end SynergyAnalytic
