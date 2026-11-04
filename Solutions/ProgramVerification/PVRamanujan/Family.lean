/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.SumAffine
import ForwardRamanujan.Math

/-!
# The Ramanujan-budget family on the shared contract

A Ramanujan-budget provider proves, for parameters `(m, M, A, Y)` and a bound `C`,

  `∀ x > exp Y, εUpper(M, x) − εLower(m, exp A, x) ≤ C`

(`DudekPlatt.v3`, Lemma 2.1 repaired). `ForwardRamanujan.epsilon_majorant` reduces the left side
to `upper m M A Y = Σ terms − 134 − max 0 m`. The selected C program computes
`4096 · Σ xᵢ − 134 − max 0 m`, where the literals `xᵢ` round the terms upward after division by
4096.

This file states that reduction once for every instance. An instance supplies only its selected
file, its literals and its parameters; `budgetCheck` is its single certificate, and
`budget_of_check` is the theorem. Before this file, each of the six instances
(`ForwardRamanujan.Old`, `.Updated`, `.OldGrouped`, `.UpdatedGrouped`, pilot `OldB`, `NewB`)
carried its own 122-line copy of the glue proofs.

Small example: `RamanujanNumerics.v2` has `(m, M, A, Y) = (119, 131, 3914, 3915)` and
`C = 9.101`. Its seven terms start `2·131 = 262` and `(2·131 + 132)/3915`.
-/

namespace PVRamanujan

open Real PVCore

/-- `ForwardRamanujan.terms` in exact rationals. -/
def termsQ (m M A Y : ℚ) : List ℚ :=
  [2 * M, (2 * M + 132) / Y, (4 * M + 288) / Y ^ 2, (12 * M + 576) / Y ^ 3, 48 * M / Y ^ 4,
    M ^ 2 / Y ^ 5, max 0 (-m) * (1 + 1 / A) ^ 6]

theorem termsQ_sum_cast (m M A Y : ℚ) :
    (((termsQ m M A Y).sum : ℚ) : ℝ) = (ForwardRamanujan.terms m M A Y).sum := by
  simp only [termsQ, ForwardRamanujan.terms, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- The selected wrapper `ramanujan_epsilon_bound` of every Ramanujan-budget provider. -/
def program (literals : List String) (scale fixed positive : String) : Program :=
  ⟨"ramanujan_epsilon_bound", literals, scale, [(.minus, fixed), (.minus, positive)]⟩

/-- The one certificate of an instance: the shared program check, the two constants are `134`
and `max 0 m`, the literals enclose the terms after scaling, and output plus proved error is at
most `bound`. -/
def budgetCheck (src : String) (p : Program) (m M A Y eps bound : ℚ) : Bool :=
  check src p eps && decide ((valuesOf p).ops = [(.minus, 134), (.minus, max 0 m)]) &&
    decide ((termsQ m M A Y).sum ≤ (valuesOf p).scale * (valuesOf p).xs.sum) &&
    decide (0 ≤ M) && decide (0 < Y) &&
    decide ((valuesOf p).out + forwardError (valuesOf p).scale (valuesOf p).s eps
      (valuesOf p).xs.length ≤ bound)

/-- **Family theorem.** A passing certificate proves the budget inequality on the whole ray. -/
theorem budget_of_check {src : String} {p : Program} {m M A Y eps bound : ℚ}
    (h : budgetCheck src p m M A Y eps bound = true) :
    ∀ x > exp (Y : ℝ), DudekPlatt.v3.εUpper (M : ℝ) x -
      DudekPlatt.v3.εLower (m : ℝ) (exp (A : ℝ)) x ≤ (bound : ℝ) := by
  simp only [budgetCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, hops⟩, henc⟩, hM⟩, hY⟩, hb⟩ := h
  obtain ⟨-, -, -, -, hup, -⟩ := certified hc
  intro x hx
  have hlog : (Y : ℝ) ≤ log x := by
    have h' := log_lt_log (exp_pos _) hx
    rw [log_exp] at h'
    exact h'.le
  have hmaj : DudekPlatt.v3.εUpper (M : ℝ) x - DudekPlatt.v3.εLower (m : ℝ) (exp (A : ℝ)) x ≤
      ForwardRamanujan.upper m M A Y :=
    ForwardRamanujan.epsilon_majorant (by exact_mod_cast hM) (by exact_mod_cast hY) hlog
  have hval : ForwardRamanujan.upper m M A Y = (((termsQ m M A Y).sum - 134 - max 0 m : ℚ) : ℝ) := by
    rw [ForwardRamanujan.upper, ← termsQ_sum_cast]
    push_cast
    ring
  rw [hops] at hup
  simp only [exactValue, opsValue, Sign.apply] at hup
  have hq : (termsQ m M A Y).sum - 134 - max 0 m ≤ bound := by linarith
  calc DudekPlatt.v3.εUpper (M : ℝ) x - DudekPlatt.v3.εLower (m : ℝ) (exp (A : ℝ)) x
      ≤ ForwardRamanujan.upper m M A Y := hmaj
    _ = (((termsQ m M A Y).sum - 134 - max 0 m : ℚ) : ℝ) := hval
    _ ≤ (bound : ℝ) := by exact_mod_cast hq

end PVRamanujan
