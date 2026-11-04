/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
/-! Preserved seven-term workload, instantiated only after the old baseline freeze. -/
namespace RamanujanNumerics.v2
open Real DudekPlatt.v3
/-- Deterministically rounded output-plus-error allowance; exact value from the new source certificate. -/
noncomputable def allowance : ℝ := (9101:ℝ)/1000
/-- Updated numerical majorant for the same repaired criterion and common full ray.

Spelled out: for every real `x > exp 3915`,
`εUpper(131, x) − εLower(119, exp 3914, x) ≤ allowance = 9.101`, where `εUpper` and `εLower` are
the seventh-order terms of `DudekPlatt.v3` (Dudek–Platt Lemma 2.1, repaired). This is pure
arithmetic and has no analytic premise. `131` and `119` are the coefficients that
`DudekPlattNumerics.v5` proves from the QRH-derived `ψ` bound, and the consumer is
`RamanujanGap.v2`.

How it is checked: the C program `Solutions/RamanujanNumerics.v2/c/updated.c` sums seven
upward-rounded binary64 terms, multiplies by 4096 and subtracts 134 and 119. Its RN64 execution
and generic summation error bound give the inequality. Trust: six finite `native_decide` facts,
which is not official three-axiom compliance; compiler and hardware are trusted. Walkthrough:
`docs/qrh/RAMANUJAN_WALKTHROUGH.md`. -/
def epsilon_budget : Prop := ∀ x>exp 3915,
  εUpper 131 x-εLower 119 (exp 3914) x≤allowance
end RamanujanNumerics.v2
