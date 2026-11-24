/- General CMS functional source transport; definitions live in the
Mathlib-only core vocabulary. See SOURCE_LEDGER.html for primary formulas. -/
import IEANTN.Vocabulary.CMSFunctional
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter IEANTN.CMSFunctional
namespace RHOnePrime.CMSFunctional

lemma exterior_eq_compl : exterior = (Icc (-1 : ℝ) 1)ᶜ := by
  ext x
  simp only [exterior, mem_setOf_eq, mem_compl_iff, mem_Icc]
  rw [← abs_le]
  exact lt_iff_not_ge

lemma paper_gap_shift (n : ℕ) : paperNormalizedGap (n+1) = normalizedGap n := by
  simp [paperNormalizedGap, paperPrime, normalizedGap, primeAt]

/-- The one-based source indexing is formally transported to zero-based Nat.nth. -/
theorem zero_based_of_paper {c : ℝ} (h : PaperEventualGapBound c) : EventualGapBound c := by
  intro ε hε
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (h ε hε)
  apply Filter.eventually_atTop.2
  refine ⟨N,fun n hn => ?_⟩
  have hp := hN (n+1) (by omega)
  simpa only [paper_gap_shift] using hp

lemma bound_mono {a b : ℝ} (h : EventualGapBound a) (hab : a ≤ b) :
    EventualGapBound b := by
  intro ε hε
  exact (h ε hε).mono (fun n hn => by linarith)

/-- The actual scalar monotonicity used in the written C+(B) source derivation:
if an admissible score d/m is below the source supremum C, inversion gives the
claimed inverse-functional upper bound. -/
lemma reciprocal_supremum_transfer {m d C : ℝ} (hm : 0 < m) (hd : 0 < d)
    (hC : d/m ≤ C) : 1/C ≤ m/d := by
  have hCpos : 0 < C := (div_pos hd hm).trans_le hC
  apply (div_le_div_iff₀ hCpos hd).mpr
  have hmC := (div_le_iff₀ hm).mp hC
  nlinarith

theorem gap_from_functional (hCMS : SourceCMSFunctional) {F G : ℝ → ℝ}
    (h : Eligible F G) (hd : 0 < denominator F G) (rh : RiemannHypothesis) :
    EventualGapBound (inverseObjective F G) :=
  zero_based_of_paper (hCMS F G h hd rh)

#print axioms paper_gap_shift
#print axioms zero_based_of_paper
#print axioms reciprocal_supremum_transfer
#print axioms gap_from_functional
end RHOnePrime.CMSFunctional
