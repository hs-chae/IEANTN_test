/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import TwoBackend.Link

/-!
# The data link at `e^330` for any decaying `π` coefficient up to `1/100`

`PVThreeChain.pi_input_330` is the instance `K = 0.0098163`. Here the same reading holds for every
`K ≤ 1/100`: `|π − Li| ≤ K·x^{7/8}/log x ≤ 10⁻³·x/log⁶x` once `log x ≥ 330`, so the budget's
five-term input `(119.99, 122.5)` holds above `e^330` whatever transported coefficient arrives. A changed
upstream input that keeps `K ≤ 1/100` therefore leaves the budget program untouched.
-/

namespace PVThreeChain

open Real IEANTN

theorem pi_input_330_of {K : ℝ} (hK : K ≤ 1 / 100)
    (hA : HasPowerLogBound Eπ K 0 (7 / 8) (exp 330)) :
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
    have hkey : K * exp (-(1 / 8) * log x) * (x / log x) =
        (K * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := by
      field_simp
    have hc : K * (log x ^ 5 * exp (-(1 / 8) * log x)) ≤ (1 / 1000 : ℝ) := by
      have hn : (1 / 100 : ℝ) * (296 ^ 5 * 0.3678794412 ^ 37) ≤ 1 / 1000 := by norm_num
      have hq0 : 0 ≤ log x ^ 5 * exp (-(1 / 8) * log x) := by positivity
      calc K * (log x ^ 5 * exp (-(1 / 8) * log x))
          ≤ 1 / 100 * (log x ^ 5 * exp (-(1 / 8) * log x)) := by gcongr
        _ ≤ 1 / 100 * (296 ^ 5 * 0.3678794412 ^ 37) := by gcongr
        _ ≤ 1 / 1000 := hn
    have hu : 0 ≤ x / log x ^ 6 := by positivity
    calc |primeCounting x - Li x| = Eπ x * (x / log x) := hE
      _ ≤ K * exp (-(1 / 8) * log x) * (x / log x) := by gcongr
      _ = (K * (log x ^ 5 * exp (-(1 / 8) * log x))) * (x / log x ^ 6) := hkey
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

end PVThreeChain
