/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.MomentSemantics
import HighAnchorIntervalB.MomentRuns
namespace HighAnchorIntervalB.Numerical
open Real LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem moment_cap (i:Fin cells) :
    HighAnchorIntervalB.factorReal (HighAnchorIntervalB.sigma i)≤(momentCap i:ℝ) := by
  have hc : acceptUpper [momentOutput i] [momentCap i]=true := by
    simp [acceptUpper,momentCap,IntervalDyadic.upperBoundedBy,moment_domains i]
  have h := source_linked_upper [momentRow i] [momentOutput i] [momentCap i] (moment_execution i) hc
  simpa only [value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    Rat.cast_add,Rat.cast_zero,momentRow_semantics] using h

theorem gridBudget_le : HighAnchorIntervalB.gridBudget momentCap≤(94/100:ℝ) := by
  have h := source_linked_upper budgetProgram [budgetOutput] [target] budget_execution budget_checked
  rw [budget_semantics] at h
  norm_num [target] at h ⊢
  exact h

theorem high330_le : HighAnchorIntervalB.high 330≤(94/100:ℝ) :=
  (HighAnchorIntervalB.high330_le_gridBudget momentCap moment_cap).trans gridBudget_le

#print axioms moment_cap
#print axioms gridBudget_le
#print axioms high330_le
end HighAnchorIntervalB.Numerical
