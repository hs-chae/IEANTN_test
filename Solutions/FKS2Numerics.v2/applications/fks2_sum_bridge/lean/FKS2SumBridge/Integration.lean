import FKS2SumBridge.Specification

namespace FKS2SumBridge
open FKS2Scalar SumStability

/-- Determinism of the original evaluator at the actual first-loop source entry. -/
theorem first_loop_result_unique {final : Frame} {events : List HelperEvent}
    (hRun : (evalStmt round64 selectedAST 1018 initialLoops.1 loop1Stmt).run initialLoops.2 =
      some (final, events)) : final = trace1.result := by
  exact congrArg Prod.fst (Option.some.inj
    (hRun.symm.trans source_trace_execution.2.2.2.1))

/-- The second entry is the actual source result and helper-event state of the first loop. -/
theorem second_loop_result_unique {final : Frame} {events : List HelperEvent}
    (hRun : (evalStmt round64 selectedAST 1017 trace1.result loop2Stmt).run trace1.events =
      some (final, events)) : final = trace2.result := by
  exact congrArg Prod.fst (Option.some.inj
    (hRun.symm.trans source_trace_execution.2.2.2.2.1))

theorem first_loop_forward_error {final : Frame} {events : List HelperEvent}
    (hRun : (evalStmt round64 selectedAST 1018 initialLoops.1 loop1Stmt).run initialLoops.2 =
      some (final, events)) :
    |((get final.env "s1").getD 0 : ℝ) - FKS2Scalar.sum1| ≤ (specError1 : ℝ) := by
  rw [first_loop_result_unique hRun]
  exact rational_specification_errors.1

theorem second_loop_forward_error {final : Frame} {events : List HelperEvent}
    (hRun : (evalStmt round64 selectedAST 1017 trace1.result loop2Stmt).run trace1.events =
      some (final, events)) :
    |((get final.env "s2").getD 0 : ℝ) - FKS2Scalar.sum2| ≤ (specError2 : ℝ) := by
  rw [second_loop_result_unique hRun]
  exact rational_specification_errors.2

/-- New total budget consumes the rational specification bounds, not the prior final budget. -/
def bridgeError : ℚ :=
  coefficientError + suffixError + sensitivity * max specError1 specError2

/-- Finite rational budget arithmetic; this does not compare q to an ideal target or exact sum. -/
theorem integration_budget_checks :
    0 ≤ specError1 ∧ 0 ≤ specError2 ∧ 0 ≤ bridgeError ∧
    bridgeError ≤ 1 / 10 ^ 15 ∧ q + bridgeError ≤ Bpoc := by
  native_decide

theorem hybrid_error_via_specification :
    |hybrid (acc1 : ℝ) (acc2 : ℝ) - hybrid FKS2Scalar.sum1 FKS2Scalar.sum2| ≤
      (sensitivity * max specError1 specError2 : ℝ) := by
  have hc : (0 : ℝ) ≤ (sensitivity : ℝ) := by
    have hp : 0 ≤ sensitivity := mul_nonneg composition_checks.1.le
      composition_checks.2.1.le
    exact_mod_cast hp
  have hmax := (abs_max_sub_max_le_max (acc1 : ℝ) (acc2 : ℝ)
    FKS2Scalar.sum1 FKS2Scalar.sum2).trans
    (max_le_max rational_specification_errors.1 rational_specification_errors.2)
  have he : hybrid (acc1 : ℝ) (acc2 : ℝ) -
      hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 =
      (sensitivity : ℝ) *
        (max (acc1 : ℝ) (acc2 : ℝ) - max FKS2Scalar.sum1 FKS2Scalar.sum2) := by
    simp only [hybrid, sensitivity, Rat.cast_mul]
    ring
  rw [he, abs_mul, abs_of_nonneg hc]
  simpa using mul_le_mul_of_nonneg_left hmax hc

theorem whole_error_via_specification :
    |(q : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (bridgeError : ℝ) := by
  have hs : |(q : ℝ) - hybrid (acc1 : ℝ) (acc2 : ℝ)| ≤ (suffixError : ℝ) := by
    rw [hybrid_rat_eq]
    exact_mod_cast composition_checks.2.2.1
  change |(q : ℝ) - exactTarget| ≤ _
  calc
    _ ≤ |(q : ℝ) - hybrid (acc1 : ℝ) (acc2 : ℝ)| +
        |hybrid (acc1 : ℝ) (acc2 : ℝ) - exactTarget| := abs_sub_le _ _ _
    _ ≤ (suffixError : ℝ) + (|hybrid (acc1 : ℝ) (acc2 : ℝ) -
        hybrid FKS2Scalar.sum1 FKS2Scalar.sum2| +
        |hybrid FKS2Scalar.sum1 FKS2Scalar.sum2 - exactTarget|) :=
      add_le_add hs (abs_sub_le _ _ _)
    _ ≤ (suffixError : ℝ) + ((sensitivity * max specError1 specError2 : ℝ) +
        (coefficientError : ℝ)) :=
      add_le_add le_rfl (add_le_add hybrid_error_via_specification coefficient_error)
    _ = _ := by simp [bridgeError]; ring

/-- Successful original source execution implies the new stability-derived error bound. -/
theorem selected_fks2_error_via_stability {out : Rat}
    (hRun : FKS2Scalar.ExecC selectedAST out) :
    |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (bridgeError : ℝ) := by
  rw [source_result_unique hRun]
  exact whole_error_via_specification

theorem concrete_fks2_error_via_stability :
    ∃ out : Rat, FKS2Scalar.ExecC selectedAST out ∧
      |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (bridgeError : ℝ) := by
  exact ⟨q, fixed_execution, selected_fks2_error_via_stability fixed_execution⟩

theorem relaxed_upper_bound_via_stability :
    FKS2Numerics.v1.nuAsympE30 ≤ (Bpoc : ℝ) := by
  have h := (abs_le.mp whole_error_via_specification).1
  have hb : (q : ℝ) + (bridgeError : ℝ) ≤ (Bpoc : ℝ) := by
    exact_mod_cast integration_budget_checks.2.2.2.2
  linarith

/-- Full integration: file identities, both original loop executions, arbitrary successful
whole-source outputs, concrete existence, and the newly composed certified budget. -/
theorem complete_integration :
    SourceIdentity ∧
    (∀ final events,
      (evalStmt round64 selectedAST 1018 initialLoops.1 loop1Stmt).run initialLoops.2 =
        some (final, events) →
      |((get final.env "s1").getD 0 : ℝ) - FKS2Scalar.sum1| ≤ (specError1 : ℝ)) ∧
    (∀ final events,
      (evalStmt round64 selectedAST 1017 trace1.result loop2Stmt).run trace1.events =
        some (final, events) →
      |((get final.env "s2").getD 0 : ℝ) - FKS2Scalar.sum2| ≤ (specError2 : ℝ)) ∧
    (∀ out, FKS2Scalar.ExecC selectedAST out →
      |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (bridgeError : ℝ)) ∧
    (∃ out, FKS2Scalar.ExecC selectedAST out ∧
      |(out : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (bridgeError : ℝ)) ∧
    0 ≤ bridgeError ∧ bridgeError ≤ 1 / 10 ^ 15 ∧
    FKS2Numerics.v1.nuAsympE30 ≤ (Bpoc : ℝ) := by
  exact ⟨source_identity, fun _ _ h => first_loop_forward_error h,
    fun _ _ h => second_loop_forward_error h,
    fun _ h => selected_fks2_error_via_stability h, concrete_fks2_error_via_stability,
    integration_budget_checks.2.2.1, integration_budget_checks.2.2.2.1,
    relaxed_upper_bound_via_stability⟩

end FKS2SumBridge
