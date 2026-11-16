import SynergyAnalytic.TangentTotalModel
import SynergyAnalytic.TangentTargetWords
namespace SynergyAnalytic
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
open BoxModel
set_option autoImplicit false
set_option maxHeartbeats 0

/-- All three universal Gaussian/log caps, proved unconditionally using an
exhaustive272-cell integer-box kernel computation and its real soundness.
No native execution axiom, desired moment premise or C-runtime fact is used.
The separate claim that the physical C++ source realizes this computation
must not be inferred from this mathematical theorem. -/
theorem tangent256_universal_basis_caps : UniversalBasisCaps (373/200) (1273/2000) (129/250) := by
  obtain ⟨v,hv,hzero,hone,htwo⟩:=sourceBasis256_target_words
  have hs:=sourceBasis_sound 256 hv
  change RealBox.Contains p v.1 (tangentBasisZero 16 256) ∧
    RealBox.Contains p v.2.1 (tangentBasisOne 256) ∧
    RealBox.Contains p v.2.2 (tangentBasisTwo 256) at hs
  have hp:=RealBox.scale_real_pos p
  apply basis_caps_from_tangent_sums (pre:=16) (n:=256) (by decide) (by decide)
  · have hw : (v.1.hi:ℝ)*200 ≤ 373*(scale p:ℝ) := by exact_mod_cast hzero
    nlinarith [hs.1.2]
  · have hw : (v.2.1.hi:ℝ)*2000 ≤ 1273*(scale p:ℝ) := by exact_mod_cast hone
    nlinarith [hs.2.1.2]
  · have hw : (v.2.2.hi:ℝ)*250 ≤ 129*(scale p:ℝ) := by exact_mod_cast htwo
    nlinarith [hs.2.2.2]

#print axioms tangent256_universal_basis_caps
end SynergyAnalytic
