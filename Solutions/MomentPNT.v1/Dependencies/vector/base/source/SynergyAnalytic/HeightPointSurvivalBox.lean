import SynergyAnalytic.HeightPointLogGridSurvivalEnd
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem survivalBox_sound (i : Nat) (hi : i ≤ logCellCount) :
    RealBox.Contains p (survivalBox i) (survival i) := by
  have hu := RealBox.literal_sound p (i:Int) logCellCount (by norm_num [logCellCount])
  have hh := RealBox.sub_sound one_sound (RealBox.mul_sound hu (RealBox.sub_sound one_sound survivalEnd_sound))
  simpa only [survivalBox,survival,Nat.min_eq_left hi,Int.cast_natCast] using hh

#print axioms survivalBox_sound
end SynergyAnalytic.HeightPoint
