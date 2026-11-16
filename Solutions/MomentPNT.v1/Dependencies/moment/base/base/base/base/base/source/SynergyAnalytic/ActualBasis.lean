import SynergyAnalytic.ActualMollifier
import SynergyAnalytic.Basis
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerBetaA.ActualObject
set_option maxHeartbeats 0

/-- Three universal Gaussian/log integrals control the actual source mollifier
for every height.  The theorem uses the same fixed mollifier and cumulative
mean-square source condition, rather than changing its length with a window. -/
theorem actual_mollifier_three_basis
    {T h b m1 m2 : ℝ} (hT : 0 < T) (hh : 14 ≤ h) (hb : 1 ≤ b)
    (hmean : ∀ t > 0,
      (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
        (m1*t+m2*T)*Real.log T) :
    (∫ x in (0:ℝ)..b, sourceShapeWeight h x*mollifierMassD T x) ≤
      (T*Real.log T)*(m1*(basisZero b+(2/h)*basisOne b+(1/h^2)*basisTwo b)+
        m2*universalPeak) := by
  have hr := actual_mollifier_weighted_bound hT hh hb hmean
  rwa [universal_three_basis (by linarith : h≠0) hb] at hr

#print axioms actual_mollifier_three_basis
end SynergyAnalytic
