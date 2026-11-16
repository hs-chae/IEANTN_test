import SynergyAnalytic.VectorProgram
import SynergyAnalytic.HeightPointChecks
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
open VectorExpr
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def budgetProgram : List VectorExpr.Expr := [(.rat (1) 1),(.mul (.input 4) (.input 0)),(.mul (.input 5) (.input 0)),(.mul (.input 6) (.input 0)),(.mul (.input 7) (.input 0)),(.mul (.input 8) (.input 0)),(.mul (.input 9) (.input 0)),(.mul (.input 4) (.input 1)),(.mul (.input 11) (.input 1)),(.mul (.input 12) (.input 1)),(.mul (.input 13) (.input 1)),(.mul (.input 14) (.input 1)),(.mul (.input 15) (.input 1)),(.add (.input 10) (.neg (.input 16))),(.rat (3000000000000) 1),(.inv (.input 18)),(.mul (.input 17) (.input 19)),(.rat (330) 1),(.add (.input 21) (.neg (.input 3))),(.rat (8) 1),(.inv (.input 23)),(.mul (.input 22) (.input 24)),(.expNeg (.input 25)),(.add (.input 4) (.neg (.input 26))),(.mul (.input 21) (.input 27)),(.inv (.input 22)),(.mul (.input 28) (.input 29)),(.add (.input 26) (.input 30)),(.rat (2) 1),(.mul (.input 32) (.input 20)),(.mul (.input 33) (.input 2)),(.mul (.input 34) (.input 31))]
def budgetOutputIndex : Nat := 35
def dataC (i:Nat) : Int := cWords[i]?.getD 0+21600*scale p
def dataD (i:Nat) : Int := DWords[i]?.getD 0
def exactWord (z:Int) : ProofBox := ⟨z,z⟩
def budgetCell (i:Nat) : Option ProofBox := do
  let ctx := [survivalBox i,survivalBox (i+1),exactWord (dataC i),exactWord (dataD i)]
  let out ← VectorExpr.run budgetProgram ctx
  out[budgetOutputIndex]?
noncomputable def cValue (i:Nat) : ℝ := (dataC i:ℝ)/(scale p:ℝ)
noncomputable def DValue (i:Nat) : ℝ := (dataD i:ℝ)/(scale p:ℝ)
noncomputable def b4 (u v c D:ℝ) : ℝ := (1:ℝ)/1
noncomputable def b5 (u v c D:ℝ) : ℝ := (b4 u v c D)*(u)
noncomputable def b6 (u v c D:ℝ) : ℝ := (b5 u v c D)*(u)
noncomputable def b7 (u v c D:ℝ) : ℝ := (b6 u v c D)*(u)
noncomputable def b8 (u v c D:ℝ) : ℝ := (b7 u v c D)*(u)
noncomputable def b9 (u v c D:ℝ) : ℝ := (b8 u v c D)*(u)
noncomputable def b10 (u v c D:ℝ) : ℝ := (b9 u v c D)*(u)
noncomputable def b11 (u v c D:ℝ) : ℝ := (b4 u v c D)*(v)
noncomputable def b12 (u v c D:ℝ) : ℝ := (b11 u v c D)*(v)
noncomputable def b13 (u v c D:ℝ) : ℝ := (b12 u v c D)*(v)
noncomputable def b14 (u v c D:ℝ) : ℝ := (b13 u v c D)*(v)
noncomputable def b15 (u v c D:ℝ) : ℝ := (b14 u v c D)*(v)
noncomputable def b16 (u v c D:ℝ) : ℝ := (b15 u v c D)*(v)
noncomputable def b17 (u v c D:ℝ) : ℝ := (b10 u v c D)+-(b16 u v c D)
noncomputable def b18 (u v c D:ℝ) : ℝ := (3000000000000:ℝ)/1
noncomputable def b19 (u v c D:ℝ) : ℝ := (b18 u v c D)⁻¹
noncomputable def b20 (u v c D:ℝ) : ℝ := (b17 u v c D)*(b19 u v c D)
noncomputable def b21 (u v c D:ℝ) : ℝ := (330:ℝ)/1
noncomputable def b22 (u v c D:ℝ) : ℝ := (b21 u v c D)+-(D)
noncomputable def b23 (u v c D:ℝ) : ℝ := (8:ℝ)/1
noncomputable def b24 (u v c D:ℝ) : ℝ := (b23 u v c D)⁻¹
noncomputable def b25 (u v c D:ℝ) : ℝ := (b22 u v c D)*(b24 u v c D)
noncomputable def b26 (u v c D:ℝ) : ℝ := Real.exp (-(b25 u v c D))
noncomputable def b27 (u v c D:ℝ) : ℝ := (b4 u v c D)+-(b26 u v c D)
noncomputable def b28 (u v c D:ℝ) : ℝ := (b21 u v c D)*(b27 u v c D)
noncomputable def b29 (u v c D:ℝ) : ℝ := (b22 u v c D)⁻¹
noncomputable def b30 (u v c D:ℝ) : ℝ := (b28 u v c D)*(b29 u v c D)
noncomputable def b31 (u v c D:ℝ) : ℝ := (b26 u v c D)+(b30 u v c D)
noncomputable def b32 (u v c D:ℝ) : ℝ := (2:ℝ)/1
noncomputable def b33 (u v c D:ℝ) : ℝ := (b32 u v c D)*(b20 u v c D)
noncomputable def b34 (u v c D:ℝ) : ℝ := (b33 u v c D)*(c)
noncomputable def b35 (u v c D:ℝ) : ℝ := (b34 u v c D)*(b31 u v c D)
end SynergyAnalytic.HeightPoint
