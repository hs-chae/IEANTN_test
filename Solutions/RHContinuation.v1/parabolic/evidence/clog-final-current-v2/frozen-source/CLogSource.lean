/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CLogMathLower
import RamanujanPV.FiniteLogUpperExecute

/-! Actual source-first reuse of the unchanged C rpc_log_upper program.
The prior generic source-to-AST, UInt64/UInt128 operation/overflow, helper,
normalization/20-term loop and termination proofs construct real SourceExecution
objects. The new finite-input lower accuracy theorem strengthens its contract;
there is no unverified "upper minus guessed epsilon" premise.
-/
namespace CLogSource
open RamanujanPV RamanujanPV.AnalyticTransition CLogMathLower
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- The full actual C function has a source-closed execution on every required
new input, including all nested ceil and series helper calls. -/
theorem required_source_exec {n : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128) :
    FiniteLogUpperExecute.SourceExecution n (model n) := by
  have hh := normalization hn
  exact FiniteLogUpperExecute.source_execution_from_math hn (by omega) rfl hh.1 hh.2 rfl

/-- Every actual returned source word on these inputs is the proved exact model
value. The normalized state is identified by the existing uniqueness proof. -/
theorem returned_eq_model {n output : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128)
    (source : FiniteLogUpperExecute.SourceExecution n output) : output = model n := by
  obtain ⟨two0,k0,lower,upper,hp,low,high⟩ := source.normalized
  obtain ⟨t,actual⟩ := source.actual
  have eq := FiniteLogUpperExecute.completed_correct lower upper hp low high actual
  have numbers := congrArg WideScalar.Value.number eq
  change (output : Int) = (binaryLogUpper n two0 k0 : Int) at numbers
  have heq : output = binaryLogUpper n two0 k0 := Int.ofNat.inj numbers
  have hnorm := normalization hn
  have unique := FiniteLogNormalizationUnique.unique hp low high
    (show two n = 2 ^ exponent n from rfl) hnorm.1 hnorm.2
  rw [unique.1, unique.2] at heq
  exact heq

/-- Strengthened mathematical correctness of the actual C source, on the exact
new input domain. This is a source-execution theorem, not ordinary checking alone. -/
theorem source_log_two_sided {n output : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128)
    (source : FiniteLogUpperExecute.SourceExecution n output) :
    (output : ℝ) / 2 ^ 40 - 1 / 2 ^ 30 ≤ Real.log n ∧
      Real.log n ≤ (output : ℝ) / 2 ^ 40 := by
  have heq := returned_eq_model hn hN source
  constructor
  · rw [heq]
    exact model_log_lower hn hN
  · exact FiniteLogUpperExecute.source_log_upper_sound source

/-- The source-derived interval is available constructively for every required
new input; caller does not assume a successful execution or returned answer. -/
theorem all_required_source_intervals {n : ℕ} (hn : 2 ≤ n) (hN : n ≤ 128) :
    FiniteLogUpperExecute.SourceExecution n (model n) ∧
      ((model n : ℝ) / 2 ^ 40 - 1 / 2 ^ 30 ≤ Real.log n ∧
        Real.log n ≤ (model n : ℝ) / 2 ^ 40) := by
  have run := required_source_exec hn hN
  exact ⟨run, source_log_two_sided hn hN run⟩

#print axioms source_log_two_sided
#print axioms all_required_source_intervals
end CLogSource
