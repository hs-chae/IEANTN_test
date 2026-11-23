import ActualFullPolynomial
import CoefficientPV

/-! The unchanged executable rh_coeff.c is now consumed by the actual analytic
lower envelope. Unlike historical GapFromSource.full_machine_gap, no htrunc
analytic success premise remains. This is a source-first PV component plus a
kernel analytic consumer, not PV of the whole finite-prime-count pipeline. -/
namespace RHContinuation.Ramanujan
open Real Finset IEANTN Ramanujan640 Ramanujan640.Polynomial

noncomputable def coefficientOutput (j : ℕ) : ℝ :=
  (((RamanujanPV.FiniteScalarEval.returnedValue CoefficientPV.noneP CoefficientPV.noneC 150
    CoefficientPV.fn.body (CoefficientPV.start j)).getD
      (RamanujanPV.FiniteScalarMachine.word64 0)).number : ℝ)

lemma coefficientOutput_eq {j : ℕ} (hj : j < 21) :
    coefficientOutput j = (lhs j:ℝ)-(rhs j:ℝ) := by
  have h := CoefficientPV.numerical ⟨j,hj⟩
  change RamanujanPV.FiniteScalarEval.returnedValue CoefficientPV.noneP CoefficientPV.noneC 150
    CoefficientPV.fn.body (CoefficientPV.start j) =
      some (RamanujanPV.FiniteScalarMachine.word64 (CoefficientPV.coeff j)) at h
  unfold coefficientOutput
  rw [h]
  have hc := CoefficientPV.order ⟨j,hj⟩
  simpa [lhs,rhs,CoefficientPV.coeff,CoefficientPV.lhs,CoefficientPV.rhs,
    Option.getD_some,RamanujanPV.FiniteScalarMachine.word64] using
      (Nat.cast_sub hc : (CoefficientPV.lhs j-CoefficientPV.rhs j:ℕ)=
        (CoefficientPV.lhs j:ℝ)-(CoefficientPV.rhs j:ℝ))

noncomputable def sourcePolynomial (u : ℝ) : ℝ :=
  ∑ j ∈ range 21, coefficientOutput j*u^j

lemma sourcePolynomial_eq (u : ℝ) : sourcePolynomial u = difference u := by
  unfold sourcePolynomial difference
  apply sum_congr rfl
  intro j hj
  rw [coefficientOutput_eq (mem_range.mp hj)]

noncomputable def sourceBase (z : ℝ) : ℝ := z^4*sourcePolynomial (1/z)-1/1000

lemma sourceBase_eq {z : ℝ} (hz : z ≠ 0) : sourceBase z = fullBase z := by
  rw [fullBase_identity hz]
  unfold sourceBase
  rw [sourcePolynomial_eq]

/-- All degree20 source-model outputs feed the real actual-li envelope.
No arbitrary analytic htrunc or li-definition predicate is assumed. -/
theorem actual_source_base {l : ℝ} (hl : 27 ≤ l) :
    sourceBase l ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
  rw [sourceBase_eq (by linarith : l ≠ 0)]
  exact actual_full_base hl

theorem coefficient_actual_source :
    LCMSourcePV.RestrictedC.SourceCorresponds CoefficientPV.render CoefficientPV.actual () :=
  CoefficientPV.source

#print axioms coefficientOutput_eq
#print axioms actual_source_base
#print axioms coefficient_actual_source
end RHContinuation.Ramanujan
