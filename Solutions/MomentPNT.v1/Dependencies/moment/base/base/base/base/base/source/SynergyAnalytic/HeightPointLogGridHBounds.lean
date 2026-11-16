import SynergyAnalytic.HeightPointLogGridDefs
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem h_range : 28 ≤ logH ∧ logH ≤ 32 := by
  have hp:=RealBox.scale_real_pos p
  have hl : 28*scale p ≤ hValue.lo := by decide +kernel
  have hh : hValue.hi ≤ 32*scale p := by decide +kernel
  have hlR : (28:ℝ)*(scale p:ℝ) ≤ (hValue.lo:ℝ) := by exact_mod_cast hl
  have hhR : (hValue.hi:ℝ) ≤ 32*(scale p:ℝ) := by exact_mod_cast hh
  constructor
  · apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [logH,mul_comm] using hlR.trans h_sound.1
  · apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [logH,mul_comm] using h_sound.2.trans hhR

end SynergyAnalytic.HeightPoint
