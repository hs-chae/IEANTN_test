/- The refined envelope consumes the actual physical output bound and the source
prefix recurrence. It is not a source-execution conjunct on a detached model theorem. -/
import SynergyHeightC.MainObservedOutput
import SynergyHeightC.MainRationalProfile
import SynergyAnalytic.RationalPNTTransfer
namespace SynergyHeightC.MainRationalRead
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem finite_from_actual_total_read {out : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented out,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768)) :
    2*(∑ i ∈ Finset.range logCellCount,
      ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
        pairedFactor (pointD i) (1/8) 330) ≤ 8433850764/1000000000000 := by
  have actual := MainFinalTotal.actual_read_identity read
  have observed : out=MainObservedOutput.total := actual.trans MainObservedOutput.total_exact
  have outputBound : realWord out.hi ≤ 8433850764/1000000000000 :=
    Eq.mpr (congrArg (fun box : ProofBox=>realWord box.hi ≤ 8433850764/1000000000000) observed)
      MainObservedOutput.observed_upper_word_bound
  have sourceSum : prefixSum logCellCount=some out :=
    (MainBudgetSourceSum.prefix_value 768 (by decide)).trans (congrArg some actual.symm)
  have finite := (actual_weight_sum_bound SourceMainWeightsV1.All.all_domains
    (out:=out) sourceSum).trans outputBound
  have form : (∑ i ∈ Finset.range logCellCount,realTerm i)=
      2*(∑ i ∈ Finset.range logCellCount,
        ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
          pairedFactor (pointD i) (1/8) 330) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i member
    simp only [realTerm,mul_assoc]
  rw [form] at finite
  exact finite

theorem pi_rational_point_from_actual_total_read {out : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented out,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768))
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) :=
  pi_rational_point_of_count_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    hx MainRationalProfile.source_weights_nonnegative slopes (finite_from_actual_total_read read)
    (source_actual_height_caps MainFinalTotal.actual_running_source_family
      SourceMainWeightsV1.All.all_domains h hRH)
    h hCHJ hrvm hsmall hlow hRH hQRH

#print axioms finite_from_actual_total_read
#print axioms pi_rational_point_from_actual_total_read
end SynergyHeightC.MainRationalRead
