/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceInterfaces
namespace MertensPositive
open Real Finset ArithmeticFunction

/-- A source-independent exact test of the printed Table13 weighted-sum scaling.
The positive correction constant is bounded using only primes2,3,5. -/
theorem first_mertens_at_seven_gt : (0.4:ℝ)<A 7-Real.log 7-E := by
  have hC := correction_summable.sum_le_tsum ({2,3,5}:Finset ℕ) (fun n _ => q_nonneg n)
  have hC' : Real.log 2/2+Real.log 3/6+Real.log 5/20 ≤ correctionConstant := by
    norm_num [q] at hC
    unfold correctionConstant
    convert hC using 1 <;> first | rfl | ring
  have hprimes : primes 7=({2,3,5,7}:Finset ℕ) := by
    unfold primes
    norm_num only [Nat.floor_ofNat]
    decide
  have hA : A 7=Real.log 2/2+Real.log 3/3+Real.log 5/5+Real.log 7/7 := by
    unfold A
    rw [hprimes]
    norm_num
    ring
  have hl7L : (1.79:ℝ)<Real.log 7 := by
    have hl6 : Real.log 6=Real.log 2+Real.log 3 := by
      rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    have hm : Real.log 6<Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  have hl7U : Real.log 7<2 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have hh : (7:ℝ)<(Real.exp 1)^2 := by
      calc (7:ℝ)<(2.7182818283:ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := by gcongr; exact Real.exp_one_gt_d9
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    exact hh
  rw [hA]
  unfold E
  linarith [Real.one_half_lt_eulerMascheroniConstant,Real.log_two_gt_d9,
    Real.log_three_gt_d9,Real.log_five_gt_d9]

/-- The caption's upper bound fails at7 in its first row, if the extra log is
read literally. This does not negate the source's correctly normalized computations. -/
theorem table13_literal_caption_counterexample :
    1.851/(Real.log 7*Real.sqrt 7)<A 7-Real.log 7-E := by
  have hl7 : (1.79:ℝ)<Real.log 7 := by
    have hl6 : Real.log 6=Real.log 2+Real.log 3 := by
      rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    have hm : Real.log 6<Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  have hs : (2.64:ℝ)<Real.sqrt 7 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hp : 0<Real.log 7*Real.sqrt 7 := by positivity
  have hden : (4.7256:ℝ)<Real.log 7*Real.sqrt 7 := by nlinarith
  have hc : 1.851/(Real.log 7*Real.sqrt 7)<(0.4:ℝ) := by
    rw [div_lt_iff₀ hp]
    linarith
  exact hc.trans first_mertens_at_seven_gt

/-- The exact test point is inside the published first-row domain. -/
theorem seven_in_table13_first_row : Real.exp 1≤(7:ℝ) ∧ (7:ℝ)≤Real.exp 2 := by
  constructor
  · linarith [Real.exp_one_lt_d9]
  · have hh : (7:ℝ)<(Real.exp 1)^2 := by
      calc (7:ℝ)<(2.7182818283:ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := by gcongr; exact Real.exp_one_gt_d9
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    exact hh.le

#print axioms table13_literal_caption_counterexample
#print axioms seven_in_table13_first_row
end MertensPositive
