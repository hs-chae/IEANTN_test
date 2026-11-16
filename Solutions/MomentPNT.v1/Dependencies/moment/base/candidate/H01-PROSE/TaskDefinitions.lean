import Mathlib
noncomputable section
namespace ExposureTask
open Real MeasureTheory
open scoped Nat
noncomputable def pi (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊
noncomputable def Li2 (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, 1/Real.log t
noncomputable def Epi (x : ℝ) : ℝ := |pi x-Li2 x|/(x/Real.log x)
noncomputable def primeReciprocal (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊+1)).filter Nat.Prime, 1/(p:ℝ)
def C : ℝ := 9354674/1000000000
end ExposureTask
