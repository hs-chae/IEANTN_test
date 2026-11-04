/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujanUpdate.Input
import IEANTN.Nodes.RamanujanGap.v2.Conclusions
open Real IEANTN ForwardRamanujan

theorem RamanujanGap.v2.challenge_loss_bound
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hc : RamanujanNumerics.v2.epsilon_budget) : RamanujanGap.v2.loss_bound := by
  intro x hx
  change ForwardRamanujan.loss x≤RamanujanNumerics.v2.allowance/log x
  exact loss_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (ForwardRamanujan.Update.pi_input hp) (by norm_num [RamanujanNumerics.v2.allowance]) hx (hc x hx)

theorem RamanujanGap.v2.challenge_gap_lower_bound
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hc : RamanujanNumerics.v2.epsilon_budget) : RamanujanGap.v2.gap_lower_bound := by
  intro x hx
  change (1-RamanujanNumerics.v2.allowance/log x)*x^2/log x^6<ForwardRamanujan.gap x
  have hg := gap_from_budget (by norm_num : (0:ℝ)<3914) (by norm_num : (3914:ℝ)+1≤3915)
    (ForwardRamanujan.Update.pi_input hp) hx (hc x hx)
  have hL : 0<log x := by
    have h := log_lt_log (exp_pos (3915:ℝ)) hx
    rw [log_exp] at h
    linarith
  convert hg using 1 <;> field_simp [hL.ne'] <;> ring

theorem RamanujanGap.v2.challenge_paired
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hOld : RamanujanNumerics.v1.epsilon_budget)
    (hNew : RamanujanNumerics.v2.epsilon_budget) : RamanujanGap.v2.paired :=
  ⟨RamanujanGap.v1.challenge_loss_bound (ForwardRamanujan.Update.implies_old hp) hOld,
   RamanujanGap.v1.challenge_gap_lower_bound (ForwardRamanujan.Update.implies_old hp) hOld,
   RamanujanGap.v2.challenge_loss_bound hp hNew,
   RamanujanGap.v2.challenge_gap_lower_bound hp hNew⟩

theorem RamanujanGap.v2.challenge_strict_allowance_improvement :
    RamanujanGap.v2.strict_allowance_improvement := by
  intro x hx
  have hL : 0<log x := by
    have h := log_lt_log (exp_pos (3915:ℝ)) hx
    rw [log_exp] at h
    linarith
  exact (div_lt_div_iff_of_pos_right hL).2 (by norm_num [RamanujanNumerics.v2.allowance])
