import FKS2SumBridge.Whole

namespace FKS2SumBridge
open FKS2Scalar SumStability

/-- Both actual file identities and the original-interpreter extraction/projection chain. -/
def SourceIdentity : Prop :=
  FKS2Scalar.sourceChecked = true ∧
  SourceCorresponds SumStability.selectedSource selectedSumProgram ∧ TraceConnection ∧
  (∀ fuel st name bound inclusive body events,
    (traceLoop fuel st name bound inclusive body events).map project =
      (evalLoop round64 selectedAST fuel st name bound inclusive body).run events)

theorem source_identity : SourceIdentity :=
  ⟨FKS2Scalar.source_checked, selected_source_checked, source_trace_execution, traceLoop_project⟩

/-- Closed required summation bridge. Source terms and both accumulators are source-derived. -/
theorem complete_sum_bridge :
    SourceIdentity ∧ terms1.length = 41 ∧ terms2.length = 42 ∧
    ValidInputs terms1 ∧ ValidInputs terms2 ∧
    (∃ final, RepresentsInput (sumInitial terms1) terms1 ∧
      SumStability.ExecC selectedSumProgram (sumInitial terms1) final acc1) ∧
    (∃ final, RepresentsInput (sumInitial terms2) terms2 ∧
      SumStability.ExecC selectedSumProgram (sumInitial terms2) final acc2) ∧
    |(acc1 : ℝ) - exactSum terms1| ≤ (gamma 40 : ℝ) * sumAbs terms1 ∧
    |(acc2 : ℝ) - exactSum terms2| ≤ (gamma 41 : ℝ) * sumAbs terms2 ∧
    |(acc1 : ℝ) - FKS2Scalar.sum1| ≤ (sumError1 : ℝ) ∧
    |(acc2 : ℝ) - FKS2Scalar.sum2| ≤ (sumError2 : ℝ) := by
  exact ⟨source_identity, terms_lengths.1, terms_lengths.2, terms_valid.1, terms_valid.2,
    concrete_source_executions.1, concrete_source_executions.2, rounding_bounds.1,
    rounding_bounds.2, IEANTN_sum_errors.1, IEANTN_sum_errors.2⟩

/-- Closed whole-program endpoint with a new, nonzero generic-summation dependency path. -/
theorem complete_full_connection :
    SourceIdentity ∧ ∃ out : ℚ,
      FKS2Scalar.ExecC selectedAST out ∧
      |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (totalError : ℝ) ∧
      0 ≤ totalError ∧ totalError ≤ 1 / 10 ^ 15 ∧
      FKS2Numerics.v1.nuAsympE30 ≤ (Bpoc : ℝ) := by
  exact ⟨source_identity, q, FKS2Scalar.fixed_execution, new_whole_forward_error,
    composition_checks.2.2.2.2.2.2.1, composition_checks.2.2.2.2.2.2.2.1,
    new_relaxed_upper_bound⟩

end FKS2SumBridge
