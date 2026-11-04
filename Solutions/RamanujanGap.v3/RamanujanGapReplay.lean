/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import RamanujanGapV3.Consumer
import RamanujanBudget.Provider
import IEANTN.Nodes.DudekPlatt.v5.Conclusions

/-!
# Replays: the consumer applied to the actual program provider

* `gap_from_pi`: `RamanujanGap.v3.gap_lower_bound` with its budget premise discharged by the
  generated `RamanujanNumerics.v3` provider (one native certificate).
* `ramanujan_401_second_route`: the existing conclusion `DudekPlatt.v5.ramanujan_401` (Ramanujan's
  inequality for `x > e^401`), derived again through the program-checked budget. The network's own
  route is a bridge in the core build with standard axioms only, so this second route is weaker; it
  only shows that the program route reaches the same statement.

The π expansion `DudekPlattNumerics.v5.pi_two_sided_qrh` stays a premise, as in the node graph.
Its own solution is not imported: its closure compiles the CH2.v6 density certificates.
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
