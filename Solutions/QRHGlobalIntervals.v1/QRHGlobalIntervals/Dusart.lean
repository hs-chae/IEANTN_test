/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Criterion
import IEANTN.Nodes.Dusart2018.v1.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The middle range from Dusart's Proposition 5.4

`Dusart2018.v1.proposition_5_4` gives a prime in `(x, x + x/log³x]` for `x ≥ 89693`. On a piece
`a ≤ log x ≤ b` with `e^{b/8} ≤ c·a³` that interval is inside `(x, x + c·x^{7/8}]`, because
`x/log³x = x^{7/8}·e^{(log x)/8}/log³x ≤ x^{7/8}·e^{b/8}/a³`.
-/

namespace QRHGlobal

open Real IEANTN

/-- `e^n < 2.7182818286^n`, from Mathlib's nine-digit bound on `e`. -/
theorem exp_nat_lt (n : ℕ) (hn : n ≠ 0) : exp (n : ℝ) < 2.7182818286 ^ n := by
  have h := Real.exp_one_lt_d9
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ h (exp_pos 1).le hn

theorem dusart_piece (hD : Dusart2018.v1.proposition_5_4) {a b c : ℝ} (ha : 0 < a)
    (hab : exp (b / 8) ≤ c * a ^ 3) :
    ∀ x : ℝ, 89693 ≤ x → a ≤ log x → log x ≤ b →
      HasPrimeInInterval x (c * x ^ ((7 : ℝ) / 8)) := by
  intro x hx ha' hb'
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := ha.trans_le ha'
  apply HasPrimeInInterval.mono (hD x hx)
  have h3 : (log x) ^ (3 : ℝ) = (log x) ^ (3 : ℕ) := by exact_mod_cast rpow_natCast (log x) 3
  rw [h3, div_le_iff₀ (by positivity)]
  have hsplit : x = x ^ ((7 : ℝ) / 8) * exp (log x / 8) := by
    rw [rpow_def_of_pos hx0, ← exp_add]
    conv_lhs => rw [← exp_log hx0]
    ring_nf
  have hexp : exp (log x / 8) ≤ c * (log x) ^ 3 := by
    calc exp (log x / 8) ≤ exp (b / 8) := exp_le_exp.mpr (by linarith)
      _ ≤ c * a ^ 3 := hab
      _ ≤ c * (log x) ^ 3 := by
          have hc : 0 ≤ c := by
            have := (exp_pos (b / 8)).trans_le hab
            by_contra hneg
            push Not at hneg
            nlinarith [pow_pos ha 3]
          gcongr
  calc x = x ^ ((7 : ℝ) / 8) * exp (log x / 8) := hsplit
    _ ≤ x ^ ((7 : ℝ) / 8) * (c * (log x) ^ 3) := by gcongr
    _ = c * x ^ ((7 : ℝ) / 8) * (log x) ^ 3 := by ring

/-- `log x ≥ 11` on Dusart's range: `e^11 < 2.7182818286^11 < 59875 < 89693`. -/
theorem eleven_le_log {x : ℝ} (hx : 89693 ≤ x) : 11 ≤ log x := by
  have h := exp_nat_lt 11 (by norm_num)
  have h11 : exp (11 : ℝ) ≤ x := by
    have : (2.7182818286 : ℝ) ^ 11 < 89693 := by norm_num
    push_cast at h
    linarith
  rw [← log_exp (11 : ℝ)]
  exact log_le_log (exp_pos _) h11

/-- The middle range for `c = 1`: `89693 ≤ x ≤ e^{80}`, in two pieces `[11, 56]`, `[56, 80]`. -/
theorem dusart_range_one (hD : Dusart2018.v1.proposition_5_4) :
    ∀ x : ℝ, 89693 ≤ x → log x ≤ 80 → HasPrimeInInterval x (1 * x ^ ((7 : ℝ) / 8)) := by
  intro x hx hb
  have h11 := eleven_le_log hx
  by_cases h56 : log x ≤ 56
  · refine dusart_piece hD (a := 11) (b := 56) (by norm_num) ?_ x hx h11 h56
    calc exp ((56 : ℝ) / 8) = exp ((7 : ℕ) : ℝ) := by norm_num
      _ ≤ 2.7182818286 ^ 7 := (exp_nat_lt 7 (by norm_num)).le
      _ ≤ 1 * 11 ^ 3 := by norm_num
  · push Not at h56
    refine dusart_piece hD (a := 56) (b := 80) (by norm_num) ?_ x hx h56.le hb
    calc exp ((80 : ℝ) / 8) = exp ((10 : ℕ) : ℝ) := by norm_num
      _ ≤ 2.7182818286 ^ 10 := (exp_nat_lt 10 (by norm_num)).le
      _ ≤ 1 * 56 ^ 3 := by norm_num

end QRHGlobal
