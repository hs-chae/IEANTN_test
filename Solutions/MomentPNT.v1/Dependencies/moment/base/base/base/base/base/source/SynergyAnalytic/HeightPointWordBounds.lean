import SynergyAnalytic.HeightPointRunSound
import SynergyAnalytic.HeightPointReal
import SynergyAnalytic.HeightPointMainIdentity
import SynergyAnalytic.HeightPointGeometry
import SynergyAnalytic.HeightPointChecks
import SynergyAnalytic.EndpointCells
import SynergyAnalytic.PointCheckDecode
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive VectorExpr
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

noncomputable def baseC (i:Nat) : ℝ := (cWords[i]?.getD 0:ℝ)/(scale p:ℝ)
noncomputable def baseD (i:Nat) : ℝ := (DWords[i]?.getD 0:ℝ)/(scale p:ℝ)

theorem env_upper_at {bs:List ProofBox} {xs:List ℝ} {i:Nat} {b:ProofBox} {w:Int} {x:ℝ}
    (hs:EnvSound bs xs) (hb:bs[i]?=some b) (hreal:xs[i]?.getD 0=x) (hw:b.hi ≤ w) :
    x ≤ (w:ℝ)/(scale p:ℝ) := by
  obtain ⟨y,hy,hm⟩:=hs i b hb
  rw [hy] at hreal
  simp only [Option.getD_some] at hreal
  subst x
  have hwR : (b.hi:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw
  exact (le_div_iff₀ (RealBox.scale_real_pos p)).mpr (hm.2.trans hwR)

theorem logEndpoint_pos (i:Nat) : 0 < logEndpoint i := by
  have h0 : logEndpoint 0=logH := by
    simp only [logEndpoint,survival,Nat.zero_min,Nat.cast_zero,zero_div,zero_mul,
      sub_zero,inv_one,Real.log_one,mul_zero,add_zero]
  have hh:=logEndpoint_monotone (Nat.zero_le i)
  rw [h0] at hh
  linarith [h_range.1]

#print axioms env_upper_at
#print axioms logEndpoint_pos
end SynergyAnalytic.HeightPoint
