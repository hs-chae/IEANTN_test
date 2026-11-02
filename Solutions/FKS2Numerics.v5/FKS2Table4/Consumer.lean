/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2.v7.Conclusions
import IEANTN.Nodes.FKS2Numerics.v5.Conclusions
open Real IEANTN

theorem FKS2.v7.challenge_absolute_pi_bound (h : FKS2Numerics.v5.numerical_pi) :
    FKS2.v7.absolute_pi_bound := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hlog : 0<log x := by
    have ht := log_le_log (exp_pos (330:ℝ)) hx
    rw [log_exp] at ht
    linarith
  exact (div_le_iff₀ (div_pos hx0 hlog)).mp (h x hx)

theorem FKS2.v7.challenge_strict_allowance_improvement : FKS2.v7.strict_allowance_improvement := by
  norm_num [FKS2.v7.strict_allowance_improvement]
