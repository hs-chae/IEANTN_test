import Phase2Solution
import IEANTN.Nodes.DudekPlattNumerics.v5.Conclusions
namespace QRHPhase2
open Real IEANTN

theorem phase1_theta_strict {x : ℝ} (hx : 0 < x) :
    (0.01311 : ℝ) * x ^ (-(1 : ℝ) / 8) < 0.02 * x ^ (-(1 : ℝ) / 8) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (rpow_pos_of_pos hx _)

theorem phase1_pi_strict {x : ℝ} (hx : 0 < x) :
    (0.01323 : ℝ) * x ^ (-(1 : ℝ) / 8) < 0.021 * x ^ (-(1 : ℝ) / 8) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (rpow_pos_of_pos hx _)

theorem phase1_intervals_strict {x : ℝ} (hx : 0 < x) :
    (0.0264 : ℝ) * x ^ (7 / 8 : ℝ) < 0.08 * x ^ (7 / 8 : ℝ) := by
  exact mul_lt_mul_of_pos_right (by norm_num) (rpow_pos_of_pos hx _)

theorem registered_classical_strict {x : ℝ} (hx : exp 300 ≤ x) :
    admissibleBound 0.00000003 2 2 1 x < admissibleBound 121.096 (3/2) 2 5.5666305 x ∧
    admissibleBound 0.00000003 2 2 1 x < admissibleBound 121.0961 (3/2) 2 5.5666305 x ∧
    admissibleBound 0.00000003 2 2 1 x < admissibleBound 9.2211 (3/2) 0.84768363 1 x ∧
    admissibleBound 0.00000003 2 2 1 x < admissibleBound 0.826 0.25 1 5.5666305 x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply classical_envelope_strict <;> first | exact hx | norm_num

theorem pi_expansion_hybrid (hNew : DudekPlattNumerics.v6.pi_two_sided_144)
    (hOld : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    ∀ x : ℝ, exp 144 < x →
      DudekPlatt.v3.mainTerm x + (if exp 400 < x then 119 else 70) * x / log x ^ 6 <
        primeCounting x ∧
      primeCounting x < DudekPlatt.v3.mainTerm x +
        (if exp 400 < x then 131 else 170) * x / log x ^ 6 := by
  intro x hx
  by_cases hh : exp 400 < x
  · simpa only [if_pos hh] using hOld x hh
  · simpa only [if_neg hh] using hNew x hx
end QRHPhase2
