import Mathlib
namespace ExposureTask
open Real MeasureTheory
open scoped Nat
noncomputable def pi (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊
noncomputable def Li2 (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, 1/Real.log t
noncomputable def Epi (x : ℝ) : ℝ := |pi x-Li2 x|/(x/Real.log x)
noncomputable def paired (D L : ℝ) : ℝ := L/(L-D)-(D/(L-D))*Real.exp (-(L-D)/8)
def finiteCap : ℝ := 8433850764/1000000000000
end ExposureTask
