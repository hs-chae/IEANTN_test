import SynergyAnalytic.HeightPointLogGridHBounds
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem survivalEnd_sound : RealBox.Contains p survivalEnd endSurvival := by
  have hspan := RealBox.sub_sound (RealBox.literal_sound p 60 1 (by decide)) h_sound
  have hh := divN_sound hspan (by decide : 0<(6:Nat))
  have hh' : RealBox.Contains p (divN (sub (literal p 60 1) hValue) 6) ((60-logH)/6) := by
    simpa only [Int.cast_ofNat,Nat.cast_one,Nat.cast_ofNat,div_one,logH] using hh
  have hr := h_range
  rw [←kernel_survivalEnd]
  have hn : 0 ≤ (60-logH)/6 := by linarith [hr.2]
  have h64 : (60-logH)/6 ≤ 64 := by linarith [hr.1]
  simpa only [endSurvival,neg_div] using expNeg_sound hh' hn h64

end SynergyAnalytic.HeightPoint
