import GaussianCertificate
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RHOnePrime.GaussianKernel

def cellsConsecutive (a b : ℚ) : List GaussianCellData → Bool
  | [] => decide (a=b)
  | d::ds => decide (d.a=a) && cellsConsecutive (d.a+d.h) b ds

/-- Complete partition assembly: every accepted cell is consumed in the genuine integral. -/
theorem cells_integral_upper (absMode : Bool) (source : List ℚ)
    (ds : List GaussianCellData) (a b : ℚ)
    (hpart : cellsConsecutive a b ds = true)
    (hv : ∀ d ∈ ds, CellValid absMode source d) :
    (∫ u in (a : ℝ)..(b : ℝ), positivePartOrAbs absMode (coeffEval source u)*
      Real.exp (-(u^2))) ≤ ((ds.map GaussianCellData.upper).sum : ℚ) := by
  let f : ℝ → ℝ := fun u => positivePartOrAbs absMode (coeffEval source u)*Real.exp (-(u^2))
  have hc : Continuous f := by
    apply (continuous_positivePartOrAbs absMode source).mul
    exact Real.continuous_exp.comp (continuous_id.pow 2).neg
  change (∫ u in (a : ℝ)..(b : ℝ), f u) ≤ _
  induction ds generalizing a with
  | nil =>
    have heq : a=b := of_decide_eq_true hpart
    subst a
    simp
  | cons d ds ih =>
    obtain ⟨hda,hrest⟩ := Bool.and_eq_true_iff.mp hpart
    have hda' : d.a=a := of_decide_eq_true hda
    subst a
    have hv0 := hv d (by simp)
    have hvrest : ∀ e ∈ ds, CellValid absMode source e := by
      intro e he
      exact hv e (by simp [he])
    have htail := ih (d.a+d.h) hrest hvrest
    have hhead := cellValid_integral_upper absMode source d hv0
    change (∫ u in (d.a : ℝ)..((d.a+d.h : ℚ) : ℝ), f u) ≤ (d.upper : ℝ) at hhead
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (d.a : ℝ) ((d.a+d.h : ℚ) : ℝ))
      (hc.intervalIntegrable ((d.a+d.h : ℚ) : ℝ) (b : ℝ))
    calc
      _ = (∫ u in (d.a : ℝ)..((d.a+d.h : ℚ) : ℝ), f u) +
          (∫ u in ((d.a+d.h : ℚ) : ℝ)..(b : ℝ), f u) := hadd.symm
      _ ≤ (d.upper : ℝ)+(((ds.map GaussianCellData.upper).sum : ℚ) : ℝ) :=
        add_le_add hhead htail
      _ = (((d::ds).map GaussianCellData.upper).sum : ℚ) := by simp

#print axioms cells_integral_upper
end RHOnePrime.GaussianKernel
