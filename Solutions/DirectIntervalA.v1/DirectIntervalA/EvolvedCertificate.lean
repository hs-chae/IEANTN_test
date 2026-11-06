/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.EvolvedRuns
import DirectIntervalA.EvolvedIntegral

namespace DirectIntervalA.Evolved
open Real LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

 theorem moment_cap (i : Fin cells) : factorReal (sigma i)≤(momentCap i:ℝ) := by
  have hc : acceptUpper [momentOutput i] [momentCap i]=true := by
    simp [acceptUpper,momentCap,IntervalDyadic.upperBoundedBy,moment_domains i]
  have hh := source_linked_upper [momentRow i] [momentOutput i] [momentCap i]
    (moment_execution i) hc
  simpa only [value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    Rat.cast_add,Rat.cast_zero,momentRow_semantics] using hh

 theorem gridBudget_le : gridBudget≤(355513/1000000:ℝ) := by
  have hh := source_linked_upper budgetProgram [budgetOutput] [target]
    budget_execution budget_checked
  rw [budget_semantics] at hh
  norm_num [target] at hh ⊢
  exact hh

 theorem actualGrid_le : actualGrid≤(355513/1000000:ℝ) := by
  apply le_trans _ gridBudget_le
  unfold actualGrid gridBudget
  apply add_le_add _ le_rfl
  exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (moment_cap i) (weight_nonneg i))

 theorem high330_le : high 330≤(355513/1000000:ℝ) :=
  high330_le_actualGrid.trans actualGrid_le

 theorem baselineBudget_lower : (358513/1000000:ℝ)≤Numerical.gridBudget := by
  have hh:=source_linked_lower Numerical.budgetProgram [Numerical.budgetOutput]
    [(358513/1000000:ℚ)] Numerical.budget_execution baseline_lower_checked
  rw [Numerical.budget_semantics] at hh
  norm_num at hh ⊢
  exact hh

/-- Strict improvement between the actual two executed allowance expressions.
It bounds no prime error from below. The analytic comparison is between budgets. -/
 theorem executed_budget_gap : gridBudget+(2999/1000000:ℝ)<Numerical.gridBudget := by
  linarith [gridBudget_le,baselineBudget_lower]

/-- Exact work count for sigma cells and first-stage moment evaluations.
No wall-clock or compiler/runtime acceleration is asserted. -/
 theorem eightfold_fewer_cells : 8*cells=Numerical.cells := by decide

#print axioms high330_le
#print axioms executed_budget_gap
end DirectIntervalA.Evolved
