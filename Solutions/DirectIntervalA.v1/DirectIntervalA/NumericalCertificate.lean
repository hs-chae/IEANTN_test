/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.NumericalIntegral

namespace DirectIntervalA.Numerical
open Real LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Finite execution/domain check of all 512 actual first-stage expressions. -/
theorem moment_domains : ∀ i : Fin cells, (momentOutput i).2=true := by
  native_decide

/-- The first-stage proof derives a mathematical bound from its actual returned interval. -/
theorem moment_cap (i : Fin cells) : moment (sigma i) (U 330)≤(momentCap i:ℝ) := by
  have hc : acceptUpper [momentOutput i] [momentCap i]=true := by
    simp [acceptUpper,momentCap,IntervalDyadic.upperBoundedBy,moment_domains i]
  have hh := source_linked_upper [momentRow i] [momentOutput i] [momentCap i]
    (moment_execution i) hc
  simpa only [value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    Rat.cast_add,Rat.cast_zero,momentRow_semantics] using hh

/-- B executes with A's actual upper-endpoint rationals embedded in its syntax. -/
theorem budget_checked : acceptUpper [budgetOutput] [target]=true := by
  native_decide

theorem gridBudget_le : gridBudget≤(179257/500000:ℝ) := by
  have hh := source_linked_upper budgetProgram [budgetOutput] [target]
    budget_execution budget_checked
  rw [budget_semantics] at hh
  norm_num [target] at hh ⊢
  exact hh

/-- Both programs are materially consumed: A bounds every analytic moment and
B bounds their positively weighted sum. This is still a numerical grid theorem;
the analytic sigma-integral and final prime-interval consumers are separate. -/
theorem actualMomentGrid_le : actualMomentGrid≤(179257/500000:ℝ) := by
  apply le_trans _ gridBudget_le
  unfold actualMomentGrid gridBudget
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (moment_cap i) (weight_nonneg i))

theorem gridBudget_le_036 : gridBudget≤(9/25:ℝ) :=
  gridBudget_le.trans (by norm_num)

theorem actualMomentGrid_le_036 : actualMomentGrid≤(9/25:ℝ) :=
  actualMomentGrid_le.trans (by norm_num)

theorem high330_le : high 330≤(179257/500000:ℝ) :=
  high330_le_actualMomentGrid.trans actualMomentGrid_le

theorem high330_le_036 : high 330≤(9/25:ℝ) :=
  high330_le.trans (by norm_num)

/-- A zero-valued replacement for A's first computed cap is rejected. -/
theorem rejects_zero_first_cap :
    acceptUpper [momentOutput ⟨0,by decide⟩] [(0:ℚ)]=false := by
  native_decide

/-- Mutating the claimed cap to .35 is rejected by the same second-stage execution. -/
theorem rejects_too_small_cap : acceptUpper [budgetOutput] [(35/100:ℚ)]=false := by
  native_decide

#print axioms moment_cap
#print axioms gridBudget_le
#print axioms actualMomentGrid_le
#print axioms high330_le
end DirectIntervalA.Numerical
