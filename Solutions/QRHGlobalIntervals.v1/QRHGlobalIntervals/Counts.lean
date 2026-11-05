/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Counting
import QRHGlobalIntervals.Sixteenth
import IEANTN.Nodes.QRHPropagation.v2.Conclusions

/-!
# How many primes `(x, x + x^{7/8}]` contains, under QRH

`N(x) = π(x + x^{7/8}) − π(x)`. The prime number theorem predicts `N(x) ≈ x^{7/8}/log x`. With
`w = x^{7/8}`:

| range | input | `N·log(x + w) ≥` | `N·log x ≤` |
|---|---|---|---|
| `x ≥ e^{80}` | frontier row `(80, 0.23719)` | `0.5255·w` | `1.4745·w` |
| `x ≥ e^{300}` | frontier row `(300, 0.01310)` | `0.9737·w` | `1.0263·w` |
| `x ≥ e^{1000}` | frontier row `(1000, 0.01014)` | `0.9796·w` | `1.0204·w` |
| `x ≥ e^{300}` | Agent A's `Eπ ≤ 0.00947147·x^{-1/8}` (hypothesis) | `0.98105·w` | `1.01895·w` |

From `e^{300}` on, the interval holds between 97.4% and 102.6% of the expected number of primes
(98.1% and 101.9% with Agent A's `π` bound). The same `π` bound, through `interval_of_pi_power`,
gives a prime in `(x, x + 0.019·x^{7/8}]` for every `x ≥ e^{300}` (the network: `0.0264`; through
Agent A's `θ` coefficient: `0.0196`).
-/

namespace QRHGlobal

open Real IEANTN

/-- `e^{-n} ≤ 10^{-k}` from `10^k ≤ 2.7182818283^n`. -/
theorem exp_neg_nat_le {n k : ℕ} (h : (10 : ℝ) ^ k ≤ 2.7182818283 ^ n) :
    exp (-(n : ℝ)) ≤ 1 / 10 ^ k := by
  rw [exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  exact h.trans (exp_nat_ge n)

theorem count_80 (hθ : QRHPropagation.v2.theta_frontier) :
    ∀ x ≥ exp 80,
      0.5255 * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log (x + x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          1.4745 * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have hrow : ((80 : ℝ), (0.23719 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have h := count_of_theta_power (hθ 80 0.23719 hrow) (by norm_num) one_pos x hx
  simp only [one_mul] at h
  have he : exp (-80 / 8 : ℝ) ≤ 1 / 10 ^ 4 := by
    rw [show (-80 / 8 : ℝ) = -((10 : ℕ) : ℝ) by norm_num]
    exact exp_neg_nat_le (by norm_num)
  have he0 := exp_pos (-80 / 8 : ℝ)
  have hw := rpow_pos_of_pos ((exp_pos 80).trans_le hx) ((7 : ℝ) / 8)
  constructor
  · refine le_trans ?_ h.1
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith
  · refine h.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith

theorem count_300 (hθ : QRHPropagation.v2.theta_frontier) :
    ∀ x ≥ exp 300,
      0.9737 * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log (x + x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          1.0263 * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have hrow : ((300 : ℝ), (0.01310 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have h := count_of_theta_power (hθ 300 0.01310 hrow) (by norm_num) one_pos x hx
  simp only [one_mul] at h
  have he : exp (-300 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
    calc exp (-300 / 8 : ℝ) ≤ exp (-((37 : ℕ) : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ ≤ 1 / 10 ^ 6 := exp_neg_nat_le (by norm_num)
  have he0 := exp_pos (-300 / 8 : ℝ)
  have hw := rpow_pos_of_pos ((exp_pos 300).trans_le hx) ((7 : ℝ) / 8)
  constructor
  · refine le_trans ?_ h.1
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith
  · refine h.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith

theorem count_1000 (hθ : QRHPropagation.v2.theta_frontier) :
    ∀ x ≥ exp 1000,
      0.9796 * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log (x + x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          1.0204 * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have hrow : ((1000 : ℝ), (0.01014 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have h := count_of_theta_power (hθ 1000 0.01014 hrow) (by norm_num) one_pos x hx
  simp only [one_mul] at h
  have he : exp (-1000 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
    calc exp (-1000 / 8 : ℝ) ≤ exp (-((37 : ℕ) : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ ≤ 1 / 10 ^ 6 := exp_neg_nat_le (by norm_num)
  have he0 := exp_pos (-1000 / 8 : ℝ)
  have hw := rpow_pos_of_pos ((exp_pos 1000).trans_le hx) ((7 : ℝ) / 8)
  constructor
  · refine le_trans ?_ h.1
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith
  · refine h.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith

/-- Counting from Agent A's `π` bound (`ScopedWinnerA.pi_00947147`, under its seven named inputs),
taken as a hypothesis. -/
theorem count_from_agentA_pi
    (hπ : HasPowerLogBound Eπ (947147 / 100000000) 0 (7 / 8) (exp 300)) :
    ∀ x ≥ exp 300,
      0.98105 * x ^ ((7 : ℝ) / 8) ≤
          (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log (x + x ^ ((7 : ℝ) / 8)) ∧
        (primeCounting (x + x ^ ((7 : ℝ) / 8)) - primeCounting x) * log x ≤
          1.01895 * x ^ ((7 : ℝ) / 8) := by
  intro x hx
  have h := count_of_pi_power hπ (by norm_num) one_pos (by norm_num) x hx
  simp only [one_mul] at h
  have he : exp (-300 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
    calc exp (-300 / 8 : ℝ) ≤ exp (-((37 : ℕ) : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ ≤ 1 / 10 ^ 6 := exp_neg_nat_le (by norm_num)
  have he0 := exp_pos (-300 / 8 : ℝ)
  have hw := rpow_pos_of_pos ((exp_pos 300).trans_le hx) ((7 : ℝ) / 8)
  constructor
  · refine le_trans ?_ h.1
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith
  · refine h.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hw.le
    nlinarith

/-- **`0.019·x^{7/8}` from `e^{300}`**, from Agent A's `π` bound through the `π` route. -/
theorem intervals_from_agentA_pi
    (hπ : HasPowerLogBound Eπ (947147 / 100000000) 0 (7 / 8) (exp 300)) :
    ∀ x ≥ exp 300, HasPrimeInInterval x (0.019 * x ^ ((7 : ℝ) / 8)) := by
  refine interval_of_pi_power hπ (by norm_num) (by norm_num) (by norm_num) ?_
  have he : exp (-300 / 8 : ℝ) ≤ 1 / 10 ^ 6 := by
    calc exp (-300 / 8 : ℝ) ≤ exp (-((37 : ℕ) : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ ≤ 1 / 10 ^ 6 := exp_neg_nat_le (by norm_num)
  have he0 := exp_pos (-300 / 8 : ℝ)
  nlinarith

end QRHGlobal
