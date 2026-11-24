import OcticPhysicalWeight

/-! A genuine general primary-source input, stated independently of the octic
target: Green, The Prime Number Theorem, Definition7.1 and Theorem7.1, p40.
The source itself is not formalized. The actual smooth weight's hypotheses and
prime-population correspondence are proved, so this is explicitly B-tier.
The all-zero Mellin normalization and trivial-zero decomposition needed by the
original octic ExplicitFormula are NOT asserted as consequences here. -/
namespace RHOcticPush.GreenSource
open Real Set MeasureTheory
open scoped ContDiff
open RHOcticPush.PhysicalWeight RHOcticPush.PopulationLimit
set_option maxHeartbeats 0

/-- Exclude the pole explicitly, regardless of any totalized value of zeta at1. -/
def ProperZero := {z : ℂ // z ≠ 1 ∧ riemannZeta z = 0}

/-- Literal positive-exponent Mellin convention of source Definition7.1. -/
noncomputable def mellin (W : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (W t : ℂ) * (t : ℂ) ^ s / (t : ℂ)

noncomputable def sourcePacket (W : ℝ → ℝ) (X : ℝ) (z : ProperZero) : ℂ :=
  (IEANTN.zetaOrder z.val : ℂ) * (X : ℂ) ^ z.val * mellin W z.val

/-- An independently known *general smooth explicit formula*, not the requested
prime bound or a specific octic source predicate. Its convergence component is
justified in the source by smooth Mellin decay (Lemma 7.1, printed pp. 43–44, equations 7.8–7.11) and zero counting.
It remains a disclosed literature premise, never an axiom or claimed Lean proof. -/
def SourceGreenSmooth : Prop :=
  ∀ W : ℝ → ℝ, ContDiff ℝ ∞ W → HasCompactSupport W →
    Function.support W ⊆ Set.Ici 1 → ∀ X : ℝ, 1 < X →
      Summable (sourcePacket W X) ∧
        (((∑' k : ℕ, (ArithmeticFunction.vonMangoldt k : ℝ) * W ((k : ℝ) / X)) : ℝ) : ℂ) =
          ((X * ∫ t : ℝ, W t : ℝ) : ℂ) - ∑' z : ProperZero, sourcePacket W X z

/-- Exact general-source application to the actual admissible smooth weights.
The right side deliberately retains its source Mellin observable until its
remaining transform and trivial-zero identities have actual proofs. -/
theorem smooth_formula_from_Green (hGreen : SourceGreenSmooth) (j : ℕ) {C L : ℝ}
    (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    Summable (sourcePacket (greenWeight j C L) 2) ∧
      (smoothPopulation j C L : ℂ) =
        ((2 * ∫ t : ℝ, greenWeight j C L t : ℝ) : ℂ) -
          ∑' z : ProperZero, sourcePacket (greenWeight j C L) 2 z := by
  obtain ⟨hs, hc, hp, hX⟩ := greenWeight_admissible_on_full_ray j hC hL
  have h := hGreen (greenWeight j C L) hs hc hp 2 hX
  have hd : 0 < EvenKernel.D C L := by unfold EvenKernel.D; nlinarith [hC.1]
  have hδ : 0 < EvenKernel.δ C L := mul_pos hd (Real.exp_pos _)
  rw [green_mangoldt_sum j hδ] at h
  exact h

#print axioms smooth_formula_from_Green
end RHOcticPush.GreenSource
