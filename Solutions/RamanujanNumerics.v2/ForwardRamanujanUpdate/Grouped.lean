/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujanUpdate.OldGrouped
import ForwardRamanujanUpdate.UpdatedGrouped
import ForwardRamanujanUpdate.Input
namespace ForwardRamanujan
open Real
/-- Both fixed-target actual source programs on the identical domain, with the same target. -/
theorem grouped_old (hp : DudekPlattNumerics.v7.pi_asymmetric_pnt) : RamanujanGap.v1.loss_bound := by
  apply RamanujanGap.v1.challenge_loss_bound hp
  intro x hx
  have h := OldGrouped.epsilon_bound x hx
  norm_num [OldGrouped.m,OldGrouped.M,OldGrouped.A,OldGrouped.Y,OldGrouped.bound] at h
  linarith

theorem grouped_new (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) : RamanujanGap.v1.loss_bound := by
  intro x hx
  change loss x≤3914.7/log x
  have h := UpdatedGrouped.epsilon_bound x hx
  norm_num [UpdatedGrouped.m,UpdatedGrouped.M,UpdatedGrouped.A,UpdatedGrouped.Y,UpdatedGrouped.bound] at h
  exact loss_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (Update.pi_input hp) (by norm_num : (0:ℝ)≤3914.7) hx (by linarith)
end ForwardRamanujan
