/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Definitions
import Mathlib.Analysis.PSeries
namespace MertensPositive
open Real Finset ArithmeticFunction MeasureTheory Set

/-- Convergence of the actual all-prime correction is proved, rather than retained as a provider. -/
theorem correction_summable : PublishedCorrectionSummable := by
  have hs : Summable (fun n : ℕ => (4:ℝ)*(n:ℝ)^(-(3/2):ℝ)) :=
    ((Real.summable_nat_rpow).mpr (by norm_num : (-(3/2):ℝ) < -1)).mul_left 4
  apply Summable.of_nonneg_of_le q_nonneg _ hs
  intro n
  unfold q
  split_ifs with hp
  · have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hp.two_le
    have hn0 : (0:ℝ) < n := by linarith
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hl := Real.log_natCast_le_rpow_div n (ε := (1/2:ℝ)) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at hl
    have hl' : Real.log n ≤ 2*Real.sqrt n := by
      calc Real.log n ≤ Real.sqrt n / (1/2:ℝ) := hl
        _ = 2*Real.sqrt n := by ring
    have hden0 : 0 < (n:ℝ)*(n-1:ℝ) := mul_pos hn0 (by linarith)
    have hden : (n:ℝ)^2/2 ≤ (n:ℝ)*(n-1:ℝ) := by nlinarith
    have he : (n:ℝ)^(-(3/2):ℝ) = 1/((n:ℝ)*Real.sqrt n) := by
      rw [show (-(3/2):ℝ) = -(1+1/2) by norm_num,Real.rpow_neg hn0.le,
        Real.rpow_add hn0,Real.rpow_one,← Real.sqrt_eq_rpow]
      simp only [one_div]
    calc Real.log n / ((n:ℝ)*(n-1:ℝ)) ≤
        (2*Real.sqrt n)/((n:ℝ)*(n-1:ℝ)) := div_le_div_of_nonneg_right hl' hden0.le
      _ ≤ (2*Real.sqrt n)/((n:ℝ)^2/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4*(n:ℝ)^(-(3/2):ℝ) := by
        rw [he]
        field_simp [ne_of_gt hn0,ne_of_gt hs0]
        nlinarith [Real.sq_sqrt hn0.le]
  · positivity
#print axioms correction_summable
end MertensPositive
