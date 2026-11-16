import SynergyAnalytic.HeightPointSurvivalBox
import SynergyAnalytic.LogCellFinish
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem logCell_sound {i : Nat} {out : ProofBox} (hi : i ≤ logCellCount)
    (hr : logCell i=some out) : RealBox.Contains p out (logEndpoint i) := by
  change finishLog hValue (survivalBox i)=some out at hr
  exact finishLog_sound h_sound (survivalBox_sound i hi) hr

#print axioms logCell_sound
end SynergyAnalytic.HeightPoint
