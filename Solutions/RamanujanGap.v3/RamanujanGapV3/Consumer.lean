/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import ForwardRamanujan.Math
import IEANTN.Nodes.RamanujanGap.v3.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v5.Conclusions

/-!
# `RamanujanGap.v3` consumer theorems

The consumer theorems `ForwardRamanujan.loss_from_budget` and `gap_from_budget` (unchanged, from
`Solutions/RamanujanNumerics.v1`) at `(m, M, A, Y) = (119, 131, 400, 401)`. Standard axioms only:
the numerical work is the premise `RamanujanNumerics.v3.epsilon_budget`.
-/

open Real IEANTN ForwardRamanujan

/-- `DudekPlattNumerics.v5` in the shape the consumer theorems take, on its own range. -/
theorem RamanujanGap.v3.pi_input_400 (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    PiInput 119 131 400 := by
  constructor
  · intro x hx
    exact (hp x hx).1
  · intro x hx
    exact (hp x ((exp_lt_exp.mpr (by norm_num : (400:ℝ) < 400 + 1)).trans hx)).2

theorem RamanujanGap.v3.challenge_loss_bound
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hc : RamanujanNumerics.v3.epsilon_budget) : RamanujanGap.v3.loss_bound := by
  intro x hx
  change ForwardRamanujan.loss x ≤ RamanujanNumerics.v3.allowance / log x
  exact loss_from_budget (by norm_num : (0:ℝ) < 400) (by norm_num : (400:ℝ) + 1 ≤ 401)
    (RamanujanGap.v3.pi_input_400 hp) (by norm_num [RamanujanNumerics.v3.allowance]) hx (hc x hx)

theorem RamanujanGap.v3.challenge_gap_lower_bound
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hc : RamanujanNumerics.v3.epsilon_budget) : RamanujanGap.v3.gap_lower_bound := by
  intro x hx
  change (1 - RamanujanNumerics.v3.allowance / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x
  have hg := gap_from_budget (by norm_num : (0:ℝ) < 400) (by norm_num : (400:ℝ) + 1 ≤ 401)
    (RamanujanGap.v3.pi_input_400 hp) hx (hc x hx)
  have hL : 0 < log x := by
    have h := log_lt_log (exp_pos (401:ℝ)) hx
    rw [log_exp] at h
    linarith
  convert hg using 1 <;> field_simp [hL.ne'] <;> ring

theorem RamanujanGap.v3.challenge_ramanujan
    (hp : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hc : RamanujanNumerics.v3.epsilon_budget) : RamanujanGap.v3.ramanujan := by
  intro x hx
  have hg := gap_from_budget (by norm_num : (0:ℝ) < 400) (by norm_num : (400:ℝ) + 1 ≤ 401)
    (RamanujanGap.v3.pi_input_400 hp) hx (hc x hx)
  have hL : 401 < log x := by simpa using log_lt_log (exp_pos (401:ℝ)) hx
  have hL0 : 0 < log x := by linarith
  have hnum : 0 < log x - RamanujanNumerics.v3.allowance := by
    norm_num [RamanujanNumerics.v3.allowance]
    linarith
  have hpos : (0:ℝ) < x ^ 2 * ((log x - RamanujanNumerics.v3.allowance) / log x ^ 7) := by
    have hx0 : 0 < x := (exp_pos _).trans hx
    positivity
  unfold ForwardRamanujan.gap at hg
  linarith
