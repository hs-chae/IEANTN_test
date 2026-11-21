import RamAlgebra
import CoefficientPV

open Real IEANTN
namespace GapFromSource
noncomputable def remainderEnvelope (l : ℝ) : ℝ :=
  1 + 14/l + 145/l^2 + 1412/l^3 - 1/1000

noncomputable def coefficientPolynomial (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 21, ((CoefficientPV.lhs j : ℝ)-(CoefficientPV.rhs j : ℝ)) * u^j

/-- Actual arithmetic consumer. The analytic subtraction of the li-square
tail (unformalized here) supplies htrunc; no coefficient inequality premise. -/
theorem li_gap_from_source {l : ℝ} (hl : 1 < l)
    (htrunc : l^4*coefficientPolynomial (1/l)-1/1000 ≤
      l^4 * (l/(l-1)*RamStudy.w (l-1)-RamStudy.w l^2)) :
    remainderEnvelope l ≤ l^4 * (l/(l-1)*RamStudy.w (l-1)-RamStudy.w l^2) := by
  have h := (CoefficientPV.source_and_poly (1/l) (by positivity)).2
  change (1/l)^4+14*(1/l)^5+145*(1/l)^6+1412*(1/l)^7 ≤ coefficientPolynomial (1/l) at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ l^4 by positivity)
  have hEq : l^4*((1/l)^4+14*(1/l)^5+145*(1/l)^6+1412*(1/l)^7) =
      1+14/l+145/l^2+1412/l^3 := by
    field_simp [show l ≠ 0 by linarith] <;> ring
  rw [hEq] at hm
  unfold remainderEnvelope
  linarith

/-- End-to-end through the exact Ramanujan consumer, conditional on the
analytic remainder and the actual signed pi bounds. -/
theorem gap_from_source {l c d : ℝ} (hl : 1 < l)
    (htrunc : l^4*coefficientPolynomial (1/l)-1/1000 ≤
      l^4 * (l/(l-1)*RamStudy.w (l-1)-RamStudy.w l^2))
    (hc : RamStudy.count l ≤ RamStudy.w l-c)
    (hd : RamStudy.w (l-1)-d ≤ RamStudy.count (l-1)) :
    remainderEnvelope l-l^4*(l/(l-1)*d)+l^4*(2*RamStudy.w l*c-c^2)
      ≤ RamStudy.RG (exp l) :=
  RamStudy.signed_consumer hl (li_gap_from_source hl htrunc) hc hd

/-- The full coefficient polynomial is tied to actual C function outputs,
not to a table of predeclared coefficients. For the second numerical route
all terms j=4..20 are retained. -/
noncomputable def machinePolynomial (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 21,
    (((RamanujanPV.FiniteScalarEval.returnedValue CoefficientPV.noneP CoefficientPV.noneC 150
      CoefficientPV.fn.body (CoefficientPV.start j)).getD
        (RamanujanPV.FiniteScalarMachine.word64 0)).number : ℝ) * u^j

theorem machine_is_mathematical (u : ℝ) :
    machinePolynomial u = coefficientPolynomial u := by
  apply Finset.sum_congr rfl
  intro j hj
  have h := CoefficientPV.numerical ⟨j,Finset.mem_range.mp hj⟩
  change RamanujanPV.FiniteScalarEval.returnedValue CoefficientPV.noneP CoefficientPV.noneC 150
      CoefficientPV.fn.body (CoefficientPV.start j) =
    some (RamanujanPV.FiniteScalarMachine.word64 (CoefficientPV.coeff j)) at h
  rw [h]
  have hc := CoefficientPV.order ⟨j,Finset.mem_range.mp hj⟩
  have he :
      (CoefficientPV.coeff j : ℝ) = (CoefficientPV.lhs j : ℝ) - CoefficientPV.rhs j := Nat.cast_sub hc
  simpa [RamanujanPV.FiniteScalarMachine.word64] using congrArg (fun q : ℝ => q*u^j) he

theorem full_machine_gap {l c d : ℝ} (hl : 1 < l)
    (htrunc : l^4*coefficientPolynomial (1/l)-1/1000 ≤
      l^4 * (l/(l-1)*RamStudy.w (l-1)-RamStudy.w l^2))
    (hc : RamStudy.count l ≤ RamStudy.w l-c)
    (hd : RamStudy.w (l-1)-d ≤ RamStudy.count (l-1)) :
    l^4*machinePolynomial (1/l)-1/1000-l^4*(l/(l-1)*d)+l^4*(2*RamStudy.w l*c-c^2)
      ≤ RamStudy.RG (exp l) := by
  rw [machine_is_mathematical]
  exact RamStudy.signed_consumer hl htrunc hc hd

#print axioms machine_is_mathematical
#print axioms full_machine_gap
#print axioms gap_from_source
end GapFromSource
