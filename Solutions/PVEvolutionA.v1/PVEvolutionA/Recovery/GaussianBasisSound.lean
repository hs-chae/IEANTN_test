/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianBasisProgram

namespace PVEvolutionA.Recovery.GaussianBasis
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine
set_option maxHeartbeats 0

/-- The actual row interpreter and its soundness, with every domain flag checked.
This lemma is preflighted before the expensive concrete finite certificate. -/
theorem row_upper (i : Fin 18)
    (hc : WinnerProgramA.acceptUpper (output i) [(spec i).cap] = true) :
    WinnerProgramA.rowValue (row i) ≤ ((spec i).cap:ℝ) := by
  have h := WinnerProgramA.source_linked_upper [row i] (output i) [(spec i).cap]
    (execution i) hc
  simpa only [WinnerProgramA.value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero] using h

theorem integral_upper (i : Fin 18)
    (hc : WinnerProgramA.acceptUpper (output i) [(spec i).cap] = true) :
    (∫ y in ((spec i).start:ℝ)..((spec i).start+(spec i).step*cells),
      Gaussian.basis (spec i).n (spec i).k y) ≤ ((spec i).cap:ℝ) := by
  have hr := row_upper i hc
  have hi := Gaussian.basis_grid (spec i).n (spec i).k ((spec i).start:ℝ)
    ((spec i).step:ℝ) cells
    (by exact_mod_cast (spec i).step_nonneg)
    (by rcases (spec i).side with hk|ha;exact Or.inl hk;exact Or.inr (by exact_mod_cast ha))
  have hset : Finset.Icc 0 (cells-1)=Finset.range cells := by
    ext k;simp only [Finset.mem_Icc,Finset.mem_range];norm_num [cells];omega
  unfold WinnerProgramA.rowValue row at hr
  rw [hset] at hr
  simp only [Gaussian.cellExpr_eval] at hr
  exact hi.trans hr

#print axioms integral_upper
end PVEvolutionA.Recovery.GaussianBasis
