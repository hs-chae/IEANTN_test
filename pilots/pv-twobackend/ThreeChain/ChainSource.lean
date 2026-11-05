/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import ThreeChain.StageB331
import ThreeChain.Link330
import Table4Evolution.PowerAgentASource
import WinnerDensityA.SourceResult

/-!
# The three-program chain with a changed first input

The same chain as `PVThreeChain.gap_exceeds_leading`, with Agent A's other committed θ evaluation in
stage 1: `WinnerDensityA.source_theta300` (original inputs, `Eθ ≤ (0.009904 + 10⁻¹²)·x^{-1/8}`) in place
of `revers_source_theta300` (`0.009782`). What changes: stage 1's theorem and inputs, and stage 2's
data (`Table4Evolution.PowerAgentASource`, generated from the new coefficient alone: output
`0.0099388` instead of `0.0098163`). What does not: stage 3's program and certificate
(`StageB331`), the data link's reading (`pi_input_330_of`, any coefficient up to `1/100`), the
consumer, and the conclusion.
-/

namespace PVThreeChain

open Real IEANTN

/-- **Chain theorem, original inputs.** -/
theorem gap_exceeds_leading_source (hs : WinnerDensityA.CH2Source)
    (h : WinnerSourceContext.OriginalInputs) (hRH : RiemannHypothesisUpTo WinnerDensityA.H)
    (hqrh : ZetaZeroFreeHalfPlane (7 / 8)) (hAnchor : FKS2.v6.table4_anchor_300) :
    ∀ x > exp 331, (1 + (196 / 25) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x := by
  intro x hx
  have hθ := WinnerDensityA.source_theta300 hs h hRH hqrh
  have hπ := Table4Evolution.PowerAgentASource.pi_power hθ hAnchor
  have hpi := pi_input_330_of (by norm_num) hπ
  have hb := PVRamanujan.budget_shift (m := 11999 / 100) (by norm_num) (StageB.budget x hx)
  have hg := ForwardRamanujan.gap_from_budget (by norm_num : (0 : ℝ) < 330)
    (by norm_num : (330 : ℝ) + 1 ≤ 331) hpi hx hb
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  convert hg using 1
  field_simp
  ring

end PVThreeChain
