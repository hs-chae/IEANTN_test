import SynergyAnalytic.HeightPointGrid
import SynergyBasis.BoxRealInverse
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def logCellCount : Nat := 768
def survivalEnd : ProofBox := ⟨1855302949810796837523826334342790147,1855302949810796837523826334342790157⟩
theorem kernel_survivalEnd : expNeg (divN (sub (literal p 60 1) hValue) 6)=survivalEnd := by decide +kernel
def survivalBox (i : Nat) : ProofBox :=
  sub one (mul p (literal p i logCellCount) (sub one survivalEnd))
def logCell (i : Nat) : Option ProofBox := do
  let s := survivalBox i
  if 0 < s.lo then
    let v ← BoxModel.logPos 384 (inv p s)
    pure (add hValue (mul p (literal p 6 1) v))
  else none

noncomputable def logH : ℝ := Real.log WinnerOriginalScalars.height
noncomputable def endSurvival : ℝ := Real.exp (-(60-logH)/6)
noncomputable def survival (i : Nat) : ℝ := 1-((min i logCellCount:Nat):ℝ)/logCellCount*(1-endSurvival)
noncomputable def logEndpoint (i : Nat) : ℝ := logH+6*Real.log (survival i)⁻¹
noncomputable def heightEndpoint (i : Nat) : ℝ := Real.exp (logEndpoint i)

end SynergyAnalytic.HeightPoint
