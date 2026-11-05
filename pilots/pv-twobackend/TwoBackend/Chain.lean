/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import TwoBackend.Link
import TwoBackend.StageB
import ScopedWinnerA.Result

/-!
# A three-stage chain across two backends

1. **Stage A: Agent A's dyadic provider** (`ScopedWinnerA.pi_00947147`, unchanged, 49 native facts):
   an exact dyadic interval evaluation of a generated Lean expression over 16,385 cells, consumed by
   Agent A's analytic transfer. Output contract: `|π(x) − Li(x)| ≤ 0.00947147 · x^(7/8)/log x`
   for `x ≥ e^300`, under its seven grouped inputs (below, explicit).
2. **The data link** (`pi_input_of_powerLog`, kernel-checked analysis, no native fact): that bound
   gives `π(x) ∈ mainTerm(x) + [119.99, 122.5] · x/log⁶x` on `x > e^300`.
3. **Stage B: the selected C budget program** (`StageB.certificate`, 1 native fact) at
   `(m, M, A, Y) = (0, 122.5, 300, 301)`, then the exact shift to `m = 119.99`.

Consumer: `ForwardRamanujan.gap_from_budget`, unchanged. Result: on `x > e^301`, the Ramanujan gap
exceeds its leading term `x²/log⁶x` by the factor `1 + 7.72/log x`.

**Scope.** This is conditional on Agent A's seven inputs, which are not node conclusions of the
network (two of them are Agent A's own source packages). It is a demonstration of composing two
backends through explicit contracts, not a new network conclusion: Ramanujan's inequality itself
is already a network conclusion above `e^145` (`DudekPlatt.v6.ramanujan_145`).
-/

namespace PVTwoBackend

open Real IEANTN

/-- **The data link.** Agent A's output contract, read as the five-term `π` input of stage B. -/
theorem pi_input_of_powerLog
    (hA : HasPowerLogBound Eπ (947147 / 100000000) 0 (7 / 8) (exp 300)) :
    ForwardRamanujan.PiInput (11999 / 100) (245 / 2) 300 := by
  have herr : ∀ x : ℝ, exp 300 ≤ x →
      |primeCounting x - Li x| ≤ 1 / 1000 * (x / log x ^ 6) := by
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hL : 300 ≤ log x := by
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
    have hp := poly5_exp_eighth_le (show (296 : ℝ) ≤ log x by linarith)
    have hkey : 947147 / 100000000 * exp (-(1 / 8) * log x) * (x / log x) =
        (947147 / 100000000 * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := by
      field_simp
    have hc : 947147 / 100000000 * (log x ^ 5 * exp (-(1 / 8) * log x)) ≤ (1 / 1000 : ℝ) := by
      have hn : (947147 / 100000000 : ℝ) * (296 ^ 5 * 0.3678794412 ^ 37) ≤ 1 / 1000 := by
        norm_num
      calc 947147 / 100000000 * (log x ^ 5 * exp (-(1 / 8) * log x))
          ≤ 947147 / 100000000 * (296 ^ 5 * 0.3678794412 ^ 37) := by gcongr
        _ ≤ 1 / 1000 := hn
    have hxl : 0 ≤ x / log x := by positivity
    have hu : 0 ≤ x / log x ^ 6 := by positivity
    calc |primeCounting x - Li x| = Eπ x * (x / log x) := hE
      _ ≤ 947147 / 100000000 * exp (-(1 / 8) * log x) * (x / log x) := by gcongr
      _ = (947147 / 100000000 * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := hkey
      _ ≤ 1 / 1000 * (x / log x ^ 6) := by gcongr
  have hpos : ∀ x : ℝ, exp 300 ≤ x → 0 < x / log x ^ 6 := by
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hL : 300 ≤ log x := by
      have := log_le_log (exp_pos _) hx
      rwa [log_exp] at this
    have hL0 : 0 < log x := by linarith
    positivity
  constructor
  · intro x hx
    have hx' : exp 300 ≤ x := hx.le
    have h1 := mainTerm_add_le_Li hx'
    have h2 := (abs_le.mp (herr x hx')).1
    have hu := hpos x hx'
    have e : 11999 / 100 * x / log x ^ 6 = 11999 / 100 * (x / log x ^ 6) := by ring
    rw [e]
    linarith
  · intro x hx
    have hx' : exp 300 ≤ x :=
      ((exp_lt_exp.mpr (by norm_num : (300 : ℝ) < 300 + 1)).trans hx).le
    have h1 := Li_sub_mainTerm_le hx'
    have h2 := (abs_le.mp (herr x hx')).2
    have hu := hpos x hx'
    have e : 245 / 2 * x / log x ^ 6 = 245 / 2 * (x / log x ^ 6) := by ring
    rw [e]
    linarith

/-- **Chain theorem.** On `x > e^301`, from Agent A's seven inputs through both executed programs:
`(1 + 7.72/log x) · x²/log⁶x < (e x/log x) π(x/e) − π(x)²`. -/
theorem gap_exceeds_leading
    (hCHJ : WinnerDirectKernel.OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681 / 10000) (3599 / 10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7 / 8)) :
    ∀ x > exp 301, (1 + (193 / 25) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x := by
  intro x hx
  have hpi := pi_input_of_powerLog (ScopedWinnerA.pi_00947147 hCHJ hrvm hsmall hlow h hRH hQRH)
  have hb := PVRamanujan.budget_shift (m := 11999 / 100) (by norm_num) (StageB.budget x hx)
  have hg := ForwardRamanujan.gap_from_budget (by norm_num : (0 : ℝ) < 300)
    (by norm_num : (300 : ℝ) + 1 ≤ 301) hpi hx hb
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  convert hg using 1
  field_simp
  ring

end PVTwoBackend
