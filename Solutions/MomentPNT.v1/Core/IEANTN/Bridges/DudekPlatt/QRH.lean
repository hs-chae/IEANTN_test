/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlattNumerics.v5.Conclusions
import IEANTN.Nodes.DudekPlatt.v5.Conclusions
import Mathlib.Tactic

/-! The existing repaired criterion consumes only the new pi expansion coefficients. -/
namespace DudekPlattQRH
open Real IEANTN

theorem ramanujan_401 (hpi : DudekPlattNumerics.v5.pi_two_sided_qrh)
    (hDP : DudekPlatt.v3.criterion) : DudekPlatt.v5.ramanujan_401 := by
  apply hDP 119 131 (exp 400) (exp 401)
  · linarith [add_one_le_exp (400 : ℝ)]
  · intro x hx
    exact (hpi x hx).1
  · intro x hx
    have heq : exp 1 * exp 400 = exp (401 : ℝ) := by rw [← exp_add]; norm_num
    rw [heq] at hx
    exact (hpi x ((exp_le_exp.mpr (by norm_num : (400 : ℝ) ≤ 401)).trans_lt hx)).2
  · rw [← exp_add]; norm_num
  · intro x hx
    have hl : 400 ≤ log x := by
      have h := log_lt_log (exp_pos (401 : ℝ)) hx
      rw [log_exp] at h
      linarith
    have hl0 : 0 < log x := by linarith
    have h1 : (394 : ℝ) / log x ≤ 394 / 400 := by gcongr
    have h2 : (812 : ℝ) / log x ^ 2 ≤ 812 / 400 ^ 2 := by gcongr
    have h3 : (2148 : ℝ) / log x ^ 3 ≤ 2148 / 400 ^ 3 := by gcongr
    have h4 : (6288 : ℝ) / log x ^ 4 ≤ 6288 / 400 ^ 4 := by gcongr
    have h5 : (17161 : ℝ) / log x ^ 5 ≤ 17161 / 400 ^ 5 := by gcongr
    have hup : DudekPlatt.v3.εUpper 131 x < 336 := by
      unfold DudekPlatt.v3.εUpper
      norm_num at h1 h2 h3 h4 h5 ⊢
      linarith
    have hpos : 0 ≤ 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 +
        97 / log x ^ 4 + 30 / log x ^ 5 + 8 / log x ^ 6 := by positivity
    have hlo : 325 ≤ DudekPlatt.v3.εLower 119 (exp 400) x := by
      norm_num [DudekPlatt.v3.εLower, DudekPlatt.v3.εPos]
      linarith
    linarith

end DudekPlattQRH
