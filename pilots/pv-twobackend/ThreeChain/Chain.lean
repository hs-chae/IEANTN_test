/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import ThreeChain.StageB331
import TwoBackend.Link
import Table4Evolution.PowerAgentA
import WinnerDensityA.ReversResult

/-!
# A chain of three executed programs across two backends

1. **Agent A's θ program** (`WinnerDensityA.revers_source_theta300`, unchanged): an exact dyadic
   evaluation (Agent A's evolved numerical program, native-assisted) consumed by Agent A's analytic
   transfer. Output contract: `Eθ ≤ (0.009782 + 10⁻¹²)·x^{-1/8}` on `x ≥ e^300`, under Agent A's
   named inputs (explicit below).
2. **The power-form transport** (`Table4Evolution.PowerAgentA.pi_power`, C file
   `power_agentA.c`, kernel only): with the anchor `FKS2.v6.table4_anchor_300`,
   `Eπ ≤ 0.0098163·x^{-1/8}` on `x ≥ e^330`.
3. **The Ramanujan budget** (`StageB.budget`, C file `budget_331.c`, kernel only) at
   `(0, 122.5, 330, 331)`, then the exact shift to `m = 119.99`.

The data link (`pi_input_330`, analysis, no native fact) reads stage 2's decaying bound as the five-term
`π` input of stage 3: `|π − Li| ≤ 0.0098163·x^{7/8}/log x ≤ 10⁻³·x/log⁶x` for `log x ≥ 330`. Consumer:
`ForwardRamanujan.gap_from_budget`, unchanged. Result: on `x > e^331`,
`(1 + 7.84/log x)·x²/log⁶x < (e x/log x)π(x/e) − π(x)²`.

**Why this chain did not exist before.** The constant-on-a-ray transport (`Eπ ≤ ε` for all `x ≥ e^330`)
cannot feed the budget: the budget needs `ε·log⁵x ≤ δ` for all `x`, which fails as `x → ∞`. The
power-form transport's output decays like `x^{-1/8}`, which beats `log⁵x`.

**Scope.** Conditional on Agent A's inputs (two are solution-level) and the anchor; a demonstration of
composing three verified programs, not a new network conclusion. Ramanujan's inequality is already a
network conclusion above `e^145` (`DudekPlatt.v6.ramanujan_145`).
-/

namespace PVThreeChain

open Real IEANTN

/-- **The data link** at `e^330`, from the transport's decaying `π` bound. -/
theorem pi_input_330 (hA : HasPowerLogBound Eπ 0.0098163 0 (7 / 8) (exp 330)) :
    ForwardRamanujan.PiInput (11999 / 100) (245 / 2) 330 := by
  have herr : ∀ x : ℝ, exp 330 ≤ x →
      |primeCounting x - Li x| ≤ 1 / 1000 * (x / log x ^ 6) := by
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hL : 330 ≤ log x := by
      have := log_le_log (exp_pos _) hx
      rwa [log_exp] at this
    have hL0 : 0 < log x := by linarith
    have h := hA x hx
    simp only [pow_zero, mul_one] at h
    have hE : |primeCounting x - Li x| = Eπ x * (x / log x) := by
      unfold Eπ
      field_simp
    have hr : x ^ ((7 : ℝ) / 8 - 1) = exp (-(1 / 8) * log x) := by
      rw [rpow_def_of_pos hx0]
      ring_nf
    rw [hr] at h
    have hp := PVTwoBackend.poly5_exp_eighth_le (show (296 : ℝ) ≤ log x by linarith)
    have hkey : 0.0098163 * exp (-(1 / 8) * log x) * (x / log x) =
        (0.0098163 * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := by
      field_simp
    have hc : 0.0098163 * (log x ^ 5 * exp (-(1 / 8) * log x)) ≤ (1 / 1000 : ℝ) := by
      have hn : (0.0098163 : ℝ) * (296 ^ 5 * 0.3678794412 ^ 37) ≤ 1 / 1000 := by
        norm_num
      calc 0.0098163 * (log x ^ 5 * exp (-(1 / 8) * log x))
          ≤ 0.0098163 * (296 ^ 5 * 0.3678794412 ^ 37) := by gcongr
        _ ≤ 1 / 1000 := hn
    have hu : 0 ≤ x / log x ^ 6 := by positivity
    calc |primeCounting x - Li x| = Eπ x * (x / log x) := hE
      _ ≤ 0.0098163 * exp (-(1 / 8) * log x) * (x / log x) := by gcongr
      _ = (0.0098163 * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := hkey
      _ ≤ 1 / 1000 * (x / log x ^ 6) := by gcongr
  have hpos : ∀ x : ℝ, exp 330 ≤ x → 0 < x / log x ^ 6 := by
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hL : 330 ≤ log x := by
      have := log_le_log (exp_pos _) hx
      rwa [log_exp] at this
    have hL0 : 0 < log x := by linarith
    positivity
  have h300 : ∀ x : ℝ, exp 330 ≤ x → exp 300 ≤ x := fun x hx =>
    (exp_le_exp.mpr (by norm_num)).trans hx
  constructor
  · intro x hx
    have hx' : exp 330 ≤ x := hx.le
    have h1 := PVTwoBackend.mainTerm_add_le_Li (h300 x hx')
    have h2 := (abs_le.mp (herr x hx')).1
    have hu := hpos x hx'
    have e : 11999 / 100 * x / log x ^ 6 = 11999 / 100 * (x / log x ^ 6) := by ring
    rw [e]
    linarith
  · intro x hx
    have hx' : exp 330 ≤ x :=
      ((exp_lt_exp.mpr (by norm_num : (330 : ℝ) < 330 + 1)).trans hx).le
    have h1 := PVTwoBackend.Li_sub_mainTerm_le (h300 x hx')
    have h2 := (abs_le.mp (herr x hx')).2
    have hu := hpos x hx'
    have e : 245 / 2 * x / log x ^ 6 = 245 / 2 * (x / log x ^ 6) := by ring
    rw [e]
    linarith

/-- **Chain theorem.** On `x > e^331`, through three executed programs (Agent A's θ program, the
power-form transport, the budget): `(1 + 7.84/log x)·x²/log⁶x < (e x/log x)π(x/e) − π(x)²`. -/
theorem gap_exceeds_leading (hs : WinnerDensityA.CH2Source)
    (h : WinnerSourceContext.ReversInputs) (hRH : RiemannHypothesisUpTo WinnerDensityA.H)
    (hqrh : ZetaZeroFreeHalfPlane (7 / 8)) (hAnchor : FKS2.v6.table4_anchor_300) :
    ∀ x > exp 331, (1 + (196 / 25) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x := by
  intro x hx
  -- stage 1 → stage 2 → link
  have hθ := WinnerDensityA.revers_source_theta300 hs h hRH hqrh
  have hπ := Table4Evolution.PowerAgentA.pi_power hθ hAnchor
  have hpi := pi_input_330 hπ
  -- stage 3
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
