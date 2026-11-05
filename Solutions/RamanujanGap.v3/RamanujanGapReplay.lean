/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import RamanujanGapV3.Consumer
import RamanujanBudget.Provider
import IEANTN.Nodes.DudekPlatt.v5.Conclusions
import IEANTN.Nodes.CH2.v9.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import DDExpansionSolution

/-!
# Replays: the consumer applied to the actual program provider

* `gap_from_pi`: `RamanujanGap.v3.gap_lower_bound` with its budget premise discharged by the
  generated `RamanujanNumerics.v3` provider (one native certificate).
* `ramanujan_401_second_route`: the existing conclusion `DudekPlatt.v5.ramanujan_401` (Ramanujan's
  inequality for `x > e^401`), derived again through the program-checked budget. The network's own
  route is a bridge in the core build with standard axioms only, so this second route is weaker; it
  only shows that the program route reaches the same statement.

* `gap_from_psi`, `loss_from_psi`: both conclusions with the π premise discharged too, by its actual
  solution `DudekPlattNumerics.v5.challenge_pi_two_sided_qrh`. What remains is the QRH-derived ψ
  bound `QRHCH2.v5.psi_refined_bound`.
* `gap_from_qrh`: one step further, as `QRHCH2.v5`'s own solution takes it: `CH2.v9.refined_transfer`
  applied to the zero-free half-plane `OpenAIQRH.v1.zeta_seven_eighths`.

The remaining premises are the leaves listed by `ieantn.py report` for this node (literature and
numerical inputs, and the unreceipted `CH2.v9`/`CotangentSeries.v1` solutions); they stay premises,
as in the node graph.
-/

open Real

theorem RamanujanGap.v3.gap_from_pi (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    RamanujanGap.v3.gap_lower_bound :=
  RamanujanGap.v3.challenge_gap_lower_bound hp RamanujanNumerics.v3.Provider.epsilon_budget

theorem RamanujanGap.v3.ramanujan_401_second_route (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    DudekPlatt.v5.ramanujan_401 := by
  intro x hx
  have hg := ForwardRamanujan.gap_from_budget (by norm_num : (0:ℝ) < 400)
    (by norm_num : (400:ℝ) + 1 ≤ 401) (RamanujanGap.v3.pi_input_400 hp) hx
    (RamanujanNumerics.v3.Provider.epsilon_budget x hx)
  have hL : 401 < log x := by simpa using log_lt_log (exp_pos (401:ℝ)) hx
  have hnum : 0 < log x - RamanujanNumerics.v3.allowance := by
    norm_num [RamanujanNumerics.v3.allowance]
    linarith
  have hpos : (0:ℝ) < x ^ 2 * ((log x - RamanujanNumerics.v3.allowance) / log x ^ 7) := by
    have hx0 : 0 < x := (exp_pos _).trans hx
    have hL0 : 0 < log x := by linarith
    positivity
  unfold ForwardRamanujan.gap at hg
  linarith

theorem RamanujanGap.v3.gap_from_psi (hpsi : QRHCH2.v5.psi_refined_bound) :
    RamanujanGap.v3.gap_lower_bound :=
  RamanujanGap.v3.gap_from_pi (DudekPlattNumerics.v5.challenge_pi_two_sided_qrh hpsi)

theorem RamanujanGap.v3.loss_from_psi (hpsi : QRHCH2.v5.psi_refined_bound) :
    RamanujanGap.v3.loss_bound :=
  RamanujanGap.v3.challenge_loss_bound (DudekPlattNumerics.v5.challenge_pi_two_sided_qrh hpsi)
    RamanujanNumerics.v3.Provider.epsilon_budget

theorem RamanujanGap.v3.gap_from_qrh (htr : CH2.v9.refined_transfer)
    (hq : OpenAIQRH.v1.zeta_seven_eighths) : RamanujanGap.v3.gap_lower_bound :=
  RamanujanGap.v3.gap_from_psi (htr hq)
