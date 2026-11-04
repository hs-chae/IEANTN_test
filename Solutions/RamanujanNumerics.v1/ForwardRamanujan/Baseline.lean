/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujan.Old
import ForwardRamanujan.Consumer

theorem RamanujanNumerics.v1.challenge_epsilon_budget : RamanujanNumerics.v1.epsilon_budget := by
  intro x hx
  have h := ForwardRamanujan.Old.epsilon_bound x hx
  norm_num [ForwardRamanujan.Old.m,ForwardRamanujan.Old.M,ForwardRamanujan.Old.A,
    ForwardRamanujan.Old.Y,ForwardRamanujan.Old.bound] at h
  linarith

/-- Actual consumed AND-chain: historical pi input plus the supplied source-derived numerical proof. -/
theorem ForwardRamanujan.baseline
    (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt) :
    RamanujanGap.v1.loss_bound ∧ RamanujanGap.v1.gap_lower_bound ∧ RamanujanGap.v1.ramanujan :=
  ⟨RamanujanGap.v1.challenge_loss_bound hp RamanujanNumerics.v1.challenge_epsilon_budget,
   RamanujanGap.v1.challenge_gap_lower_bound hp RamanujanNumerics.v1.challenge_epsilon_budget,
   RamanujanGap.v1.challenge_ramanujan hp RamanujanNumerics.v1.challenge_epsilon_budget⟩
