/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
/-! The `RamanujanNumerics.v2` budget, moved to the full range of its π input. -/
namespace RamanujanNumerics.v3
open Real DudekPlatt.v3
/-- Output-plus-error allowance of the selected program, rounded up to three decimals. -/
noncomputable def allowance : ℝ := (9988:ℝ)/1000
/-- The Ramanujan epsilon budget for the QRH coefficients on the whole range where they hold.

Spelled out: for every real `x > exp 401`,
`εUpper(131, x) − εLower(119, exp 400, x) ≤ allowance = 9.988`, where `εUpper` and `εLower` are
the seventh-order terms of `DudekPlatt.v3` (Dudek–Platt Lemma 2.1, repaired). Pure arithmetic, no
analytic premise.

What changed from `RamanujanNumerics.v2`: only the range. v2 states the same inequality with
`exp 3914`/`exp 3915` and the allowance 9.101. The coefficients `119` and `131` are those of
`DudekPlattNumerics.v5`, which holds for every `x > exp 400`. Starting at `exp 401` costs a larger
allowance, because the terms `(2·131 + 132)/Y, …` are evaluated at `Y = 401` instead of 3915.
The consumer is `RamanujanGap.v3`.

How it is checked: the C program `Solutions/RamanujanNumerics.v3/c/budget.c` sums seven
upward-rounded binary64 terms, multiplies by 4096 and subtracts 134 and 119. The shared contract
`PVCore` gives its execution and error bound; the family theorem `PVRamanujan.budget_of_check`
gives this inequality. Trust: one finite `native_decide` certificate, which is not official
three-axiom compliance; compiler and hardware are trusted. -/
def epsilon_budget : Prop := ∀ x>exp 401,
  εUpper 131 x-εLower 119 (exp 400) x≤allowance
end RamanujanNumerics.v3
