/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujanUpdate.Updated
import IEANTN.Nodes.RamanujanNumerics.v2.Conclusions

theorem RamanujanNumerics.v2.challenge_epsilon_budget : RamanujanNumerics.v2.epsilon_budget := by
  intro x hx
  have h := ForwardRamanujan.Updated.epsilon_bound x hx
  norm_num [ForwardRamanujan.Updated.m,ForwardRamanujan.Updated.M,ForwardRamanujan.Updated.A,
    ForwardRamanujan.Updated.Y,ForwardRamanujan.Updated.bound] at h
  unfold RamanujanNumerics.v2.allowance
  linarith
