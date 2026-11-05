/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Ladder
import QRHGlobalIntervals.Dusart
import IEANTN.Nodes.QRHPropagation.v2.Conclusions

/-!
# Under QRH, every interval `(x, x + x^{7/8}]` with `x ≥ 1` contains a prime

Four ranges, each closed by a different input:

| range | input | check |
|---|---|---|
| `1 ≤ x < 2` | the prime `2` | `x + x^{7/8} ≥ 2` |
| `2 ≤ x < 93967` | a 32-rung prime ladder | kernel-decided step inequalities, `norm_num` primality |
| `89693 ≤ x ≤ e^{80}` | `Dusart2018.v1.proposition_5_4` | `e^7 ≤ 11³`, `e^{10} ≤ 56³` |
| `x ≥ e^{80}` | `QRHPropagation.v2.theta_frontier`, row `(80, 0.23719)` | `0.2372·(2 + e^{-10}) < 1` |

The analytic inputs are node conclusions taken as hypotheses. QRH enters only through
`theta_frontier`, whose own imports end at `OpenAIQRH.v1.zeta_seven_eighths`.
-/

namespace QRHGlobal

open Real IEANTN

/-- The ladder for `c = 1`: `(p' - p)^8 ≤ p^7` at every step, from `2` past Dusart's `89693`. -/
def ladder1 : List ℕ :=
  [2, 3, 5, 7, 11, 19, 31, 47, 73, 113, 173, 263, 389, 571, 829, 1181, 1667, 2311, 3187, 4349,
    5869, 7841, 10391, 13649, 17791, 23021, 29573, 37717, 47819, 60251, 75437, 93967]

theorem ladder1_ok : ladderOK 1 1 ladder1 = true := by decide

theorem ladder1_prime : ∀ q ∈ ladder1.tail, q.Prime := by
  simp only [ladder1, List.tail_cons, List.forall_mem_cons]
  norm_num

theorem ladder_range_one :
    ∀ x : ℝ, 2 ≤ x → x < 93967 → HasPrimeInInterval x (x ^ ((7 : ℝ) / 8)) := by
  intro x h1 h2
  have := ladder_sound 1 1 (by norm_num) 2 ladder1.tail ladder1_prime ladder1_ok x
    (by norm_num; linarith) (by simpa [ladder1] using h2)
  simpa using this

theorem frontier_range_one (hθ : QRHPropagation.v2.theta_frontier)
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x ≥ exp 80, HasPrimeInInterval x (1 * x ^ ((7 : ℝ) / 8)) := by
  have hrow : ((80 : ℝ), (0.23719 : ℝ)) ∈ CH2.v6.densityFrontier := by
    norm_num [CH2.v6.densityFrontier]
  have hb := hθ 80 0.23719 hrow
  refine interval_of_theta_power hcrit hb (by norm_num) (by norm_num) ?_
  have he : exp (-80 / 8 : ℝ) ≤ 1 := by
    rw [exp_le_one_iff]; norm_num
  nlinarith

/-- **Global short intervals under QRH.** For every real `x ≥ 1` there is a prime `p` with
`x < p ≤ x + x^{7/8}`. -/
theorem global_interval (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x : ℝ, 1 ≤ x → HasPrimeInInterval x (x ^ ((7 : ℝ) / 8)) := by
  intro x hx
  by_cases h2 : x < 2
  · refine ⟨2, Nat.prime_two, by exact_mod_cast h2, ?_⟩
    have : (1 : ℝ) ≤ x ^ ((7 : ℝ) / 8) := one_le_rpow hx (by norm_num)
    push_cast
    linarith
  push Not at h2
  by_cases hl : x < 93967
  · exact ladder_range_one x h2 hl
  push Not at hl
  have hx0 : 0 < x := by linarith
  by_cases h80 : log x ≤ 80
  · simpa using dusart_range_one hD x (by linarith) h80
  push Not at h80
  have hx80 : exp 80 ≤ x := by
    rw [← exp_log hx0]; exact exp_le_exp.mpr h80.le
  simpa using frontier_range_one hθ hcrit x hx80

/-- The same statement as a bound on prime gaps: after every prime `p` the next prime is at most
`p + p^{7/8}`. -/
theorem prime_gap_le (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {p : ℕ} (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ (q : ℝ) ≤ p + (p : ℝ) ^ ((7 : ℝ) / 8) := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  obtain ⟨q, hq, hpq, hle⟩ := global_interval hθ hD hcrit p h1
  exact ⟨q, hq, by exact_mod_cast hpq, hle⟩

end QRHGlobal
