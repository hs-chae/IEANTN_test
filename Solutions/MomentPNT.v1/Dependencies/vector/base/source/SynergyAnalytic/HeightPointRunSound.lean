import SynergyAnalytic.HeightPointConstants
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive VectorExpr
set_option autoImplicit false
set_option maxHeartbeats 0

theorem constantValues_sound : constantValues.length=realConstants.length ∧ EnvSound constantValues realConstants := by
  exact VectorExpr.run_sound constantProgram (by rfl)
    (by intro i b h;cases i <;> simp at h) kernel_constants

theorem point_sound {t : ProofBox} {out : List ProofBox} {x : ℝ}
    (hx : RealBox.Contains p t x) (hr : point constantValues t=some out) :
    out.length=(realPoint x).length ∧ EnvSound out (realPoint x) := by
  apply VectorExpr.run_sound pointProgram (input:=constantValues++[t]) (xs:=realConstants++[x]) (out:=out)
  · simp only [List.length_append,List.length_singleton,constantValues_sound.1]
  · exact VectorExpr.env_append constantValues_sound.1 constantValues_sound.2 hx
  · exact hr

#print axioms constantValues_sound
#print axioms point_sound
end SynergyAnalytic.HeightPoint
