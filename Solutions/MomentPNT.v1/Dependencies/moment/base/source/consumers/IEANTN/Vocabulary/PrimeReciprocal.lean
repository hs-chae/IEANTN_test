/- Shared mathematical object only. No theorem or source-program assumption. -/
import IEANTN.Vocabulary.PrimeCounting
namespace IEANTN
open scoped Nat
noncomputable def primeReciprocal (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊+1)).filter Nat.Prime, 1/(p:ℝ)
end IEANTN
#print axioms IEANTN.primeReciprocal
