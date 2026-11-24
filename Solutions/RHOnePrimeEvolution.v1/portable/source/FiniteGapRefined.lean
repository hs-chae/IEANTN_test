/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FiniteGapSourceConsumer

namespace RHOnePrime.FiniteGap
open Real
set_option maxHeartbeats 0

lemma exp12_gt_162000 : (162000 : ℝ) < exp 12 := by
  have he : (1359 / 500 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow : (1359 / 500 : ℝ) ^ 12 < (exp (1 : ℝ)) ^ 12 :=
    pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have h12 : exp (12 : ℝ) = (exp (1 : ℝ)) ^ 12 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 12
  rw [h12]
  norm_num at hpow ⊢
  linarith

lemma width_exceeds_1550_refined {c x : ℝ} (hc : (1 / 2500 : ℝ) ≤ c)
    (hx : exp 24 ≤ x) : 1550 < c * sqrt x * log x := by
  have hx0 : 0 ≤ x := (exp_pos 24).le.trans hx
  have he : (exp (12 : ℝ)) ^ 2 = exp 24 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hs : (162000 : ℝ) < sqrt x := by
    have hs' : exp 12 ≤ sqrt x := by
      nlinarith [sq_sqrt hx0, sqrt_nonneg x, exp_pos (12 : ℝ)]
    exact exp12_gt_162000.trans_le hs'
  have hl : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
  have hm : (324 / 5 : ℝ) < c * sqrt x := by nlinarith
  nlinarith

theorem finite_constant_window (hgap : SourceGapB) {x : ℝ}
    (hx : exp 24 ≤ x) (hx44 : x < exp 44) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + 1551 := by
  apply prime_in_real_interval RHOnePrimeEvolution.FiniteEndpoint.terminal_prime
    (source_gap_to_terminal hgap) _ (hx44.trans exp44_lt_terminal) (by norm_num)
  linarith [exp24_large.trans_le hx]

theorem finite_coefficient_0004 (hgap : SourceGapB) {c x : ℝ}
    (hc : (1 / 2500 : ℝ) ≤ c) (hx : exp 24 ≤ x) (hx44 : x < exp 44) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + c * sqrt x * log x := by
  apply prime_in_real_interval RHOnePrimeEvolution.FiniteEndpoint.terminal_prime
    (source_gap_to_terminal hgap) _ (hx44.trans exp44_lt_terminal)
    (width_exceeds_1550_refined hc hx)
  linarith [exp24_large.trans_le hx]

#print axioms finite_constant_window
#print axioms finite_coefficient_0004
end RHOnePrime.FiniteGap
