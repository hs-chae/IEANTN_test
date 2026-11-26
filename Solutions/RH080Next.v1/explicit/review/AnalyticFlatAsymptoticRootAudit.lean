import AnalyticFlatFamilyAsymptoticPopulation

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Filter RH080Next.Explicit
namespace RH080Next.RootAsymptoticReview

/-- Independently expanded quantifier order: the density threshold comes
first; the prime-variable threshold may depend on the chosen density.
This is an actual prime-count statement with the original source inputs. -/
theorem actual_count_quantifiers (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (η : ℝ) (hη : 0<η) :
    ∃ A : ℝ, ∀ α : ℝ, A≤α → ∃ δ : ℝ, 0<δ ∧ ∃ X : ℝ, ∀ x : ℝ, X≤x →
      (α+δ)*Real.sqrt x≤
        ((Nat.primeCounting
          ⌊x+(α+Real.log α/Real.pi+(2+Real.log (2*Real.pi))/Real.pi+η)*Real.sqrt x*Real.log x⌋₊ -
          Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) := by
  obtain ⟨A,hA⟩ := eventually_atTop.1
    (AnalyticFlatFamilyAsymptotic.actual_population_eventual hNorm hUniform hRH η hη)
  refine ⟨A,?_⟩
  intro α hα
  obtain ⟨δ,hδ,hcount⟩ := hA α hα
  obtain ⟨X,hX⟩ := eventually_atTop.1 hcount
  exact ⟨δ,hδ,X,hX⟩

#print axioms actual_count_quantifiers
end RH080Next.RootAsymptoticReview
