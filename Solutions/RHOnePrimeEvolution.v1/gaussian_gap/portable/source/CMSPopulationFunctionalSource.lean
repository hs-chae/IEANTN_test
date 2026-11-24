import CMSFunctionalGapSource

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter IEANTN.CMSFunctional
namespace RHOnePrime.CMSFunctional

lemma normalizedPopulation_mono {c d x : ℝ} (hcd : c ≤ d) (hx : 2 ≤ x) :
    normalizedPopulation c x ≤ normalizedPopulation d x := by
  have hlog : 0 ≤ log x := log_nonneg (by linarith)
  have hfactor : 0 ≤ sqrt x*log x := mul_nonneg (sqrt_nonneg x) hlog
  have hend : x+c*sqrt x*log x ≤ x+d*sqrt x*log x := by
    nlinarith [mul_le_mul_of_nonneg_right hcd hfactor]
  have hn := Nat.monotone_primeCounting (Nat.floor_mono hend)
  have hcount : halfOpenCount c x ≤ halfOpenCount d x := by
    exact Nat.sub_le_sub_right hn _
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
  exact_mod_cast hcount

lemma goodCoefficient_mono {α c d : ℝ} (h : GoodCoefficient α c) (hcd : c ≤ d) :
    GoodCoefficient α d := by
  obtain ⟨hc,δ,hδ,hev⟩ := h
  refine ⟨hc.trans_le hcd,δ,hδ,?_⟩
  filter_upwards [hev,eventually_ge_atTop (2 : ℝ)] with x hx hx2
  exact hx.trans (normalizedPopulation_mono hcd hx2)

/-- Formal infimum/upward-closure transport. The epsilon slack is necessary;
no attainment of the infimum or strict limiting margin at equality is claimed. -/
theorem population_from_functional (hCMS : SourceCMSPopulation) {F G : ℝ → ℝ}
    (h : Eligible F G) (hd : 0 < denominator F G) (rh : RiemannHypothesis)
    {α c : ℝ} (hα : 0 ≤ α) (hc : (1+2*α)*inverseObjective F G < c) :
    GoodCoefficient α c := by
  obtain ⟨hne,hinf⟩ := hCMS F G h hd rh α hα
  obtain ⟨d,hdgood,hdc⟩ := exists_lt_of_csInf_lt hne (hinf.trans_lt hc)
  exact goodCoefficient_mono hdgood hdc.le

/-- The positive normalized margin yields a strict count of actual primes;
there is no explicit numerical onset in this asymptotic source theorem. -/
theorem eventual_count_of_good {α c : ℝ} (h : GoodCoefficient α c) :
    ∀ᶠ x : ℝ in atTop, α*sqrt x < (halfOpenCount c x : ℝ) := by
  obtain ⟨_,δ,hδ,hev⟩ := h
  filter_upwards [hev,eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hs : 0 < sqrt x := sqrt_pos.mpr (by linarith)
  have hnorm : α < normalizedPopulation c x := by linarith
  exact (lt_div_iff₀ hs).mp hnorm

#print axioms normalizedPopulation_mono
#print axioms population_from_functional
#print axioms eventual_count_of_good
end RHOnePrime.CMSFunctional
