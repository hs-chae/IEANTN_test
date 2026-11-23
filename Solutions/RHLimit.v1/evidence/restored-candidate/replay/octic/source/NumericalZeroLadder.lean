/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DiscreteZeroCount
open Real Set MeasureTheory
namespace RHContinuation.NumericalZeroLadder
open RHContinuation.DiscreteZeroCount
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem exp_lower_taylor {u r : ℝ} (hu : 0 ≤ u)
    (hr : r < ∑ i ∈ Finset.range 20, u ^ i / (Nat.factorial i : ℝ)) : r < Real.exp u :=
  hr.trans_le (Real.sum_le_exp_of_nonneg hu 20)

theorem main_t1 : ZeroCount.v1.rvmMain (9676/1000:ℝ) ≤ (0:ℝ) := by
  have hrhi : (9676/1000:ℝ)/(2*π) ≤ (604750/392699:ℝ) := by
    have hh : (9676/1000:ℝ)/(2*π) ≤ (9676/1000:ℝ)/(2*(3.141592:ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [pi_gt_d6]
    norm_num at hh ⊢
    exact hh
  have hrlo : (4838000/3141593:ℝ) ≤ (9676/1000:ℝ)/(2*π) := by
    have hh : (9676/1000:ℝ)/(2*(3.141593:ℝ)) ≤ (9676/1000:ℝ)/(2*π) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [pi_lt_d6]
    norm_num at hh ⊢
    exact hh
  have hex : (604750/392699:ℝ) < exp (21588587/50000000:ℝ) := by
    apply exp_lower_taylor (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl : log ((9676/1000:ℝ)/(2*π)) ≤ (21588587/50000000:ℝ) := by
    apply le_of_lt
    rw [log_lt_iff_lt_exp (by positivity)]
    exact hrhi.trans_lt hex
  have hn : 0 ≤ log ((9676/1000:ℝ)/(2*π)) := by
    apply log_nonneg
    have hh : (1:ℝ) ≤ (4838000/3141593:ℝ) := by norm_num
    exact hh.trans hrlo
  have hp := mul_le_mul hrhi hl hn (by norm_num : (0:ℝ) ≤ (604750/392699:ℝ))
  calc
    ZeroCount.v1.rvmMain (9676/1000:ℝ) ≤ (604750/392699:ℝ)*(21588587/50000000:ℝ)-(4838000/3141593:ℝ)+7/8 := by
      unfold ZeroCount.v1.rvmMain
      linarith
    _ ≤ 0 := by norm_num

theorem count_t1 (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (9676/1000:ℝ) ≤ (0:ℝ) :=
  by
    simpa using count_le_of_main_le hsmall (t := 9676/1000) (n := 0)
      (by norm_num) (by norm_num) (by simpa using main_t1)

theorem main_t2 : ZeroCount.v1.rvmMain (17847/1000:ℝ) ≤ (1:ℝ) := by
  have hrhi : (17847/1000:ℝ)/(2*π) ≤ (2230875/785398:ℝ) := by
    have hh : (17847/1000:ℝ)/(2*π) ≤ (17847/1000:ℝ)/(2*(3.141592:ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [pi_gt_d6]
    norm_num at hh ⊢
    exact hh
  have hrlo : (8923500/3141593:ℝ) ≤ (17847/1000:ℝ)/(2*π) := by
    have hh : (17847/1000:ℝ)/(2*(3.141593:ℝ)) ≤ (17847/1000:ℝ)/(2*π) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [pi_lt_d6]
    norm_num at hh ⊢
    exact hh
  have hex : (2230875/785398:ℝ) < exp (104395857/100000000:ℝ) := by
    apply exp_lower_taylor (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl : log ((17847/1000:ℝ)/(2*π)) ≤ (104395857/100000000:ℝ) := by
    apply le_of_lt
    rw [log_lt_iff_lt_exp (by positivity)]
    exact hrhi.trans_lt hex
  have hn : 0 ≤ log ((17847/1000:ℝ)/(2*π)) := by
    apply log_nonneg
    have hh : (1:ℝ) ≤ (8923500/3141593:ℝ) := by norm_num
    exact hh.trans hrlo
  have hp := mul_le_mul hrhi hl hn (by norm_num : (0:ℝ) ≤ (2230875/785398:ℝ))
  calc
    ZeroCount.v1.rvmMain (17847/1000:ℝ) ≤ (2230875/785398:ℝ)*(104395857/100000000:ℝ)-(8923500/3141593:ℝ)+7/8 := by
      unfold ZeroCount.v1.rvmMain
      linarith
    _ ≤ 1 := by norm_num

theorem count_t2 (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (17847/1000:ℝ) ≤ (1:ℝ) :=
  by
    simpa using count_le_of_main_le hsmall (t := 17847/1000) (n := 1)
      (by norm_num) (by norm_num) (by simpa using main_t2)

theorem main_t3 : ZeroCount.v1.rvmMain (23171/1000:ℝ) ≤ (2:ℝ) := by
  have hrhi : (23171/1000:ℝ)/(2*π) ≤ (2896375/785398:ℝ) := by
    have hh : (23171/1000:ℝ)/(2*π) ≤ (23171/1000:ℝ)/(2*(3.141592:ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [pi_gt_d6]
    norm_num at hh ⊢
    exact hh
  have hrlo : (11585500/3141593:ℝ) ≤ (23171/1000:ℝ)/(2*π) := by
    have hh : (23171/1000:ℝ)/(2*(3.141593:ℝ)) ≤ (23171/1000:ℝ)/(2*π) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [pi_lt_d6]
    norm_num at hh ⊢
    exact hh
  have hex : (2896375/785398:ℝ) < exp (2039101/1562500:ℝ) := by
    apply exp_lower_taylor (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl : log ((23171/1000:ℝ)/(2*π)) ≤ (2039101/1562500:ℝ) := by
    apply le_of_lt
    rw [log_lt_iff_lt_exp (by positivity)]
    exact hrhi.trans_lt hex
  have hn : 0 ≤ log ((23171/1000:ℝ)/(2*π)) := by
    apply log_nonneg
    have hh : (1:ℝ) ≤ (11585500/3141593:ℝ) := by norm_num
    exact hh.trans hrlo
  have hp := mul_le_mul hrhi hl hn (by norm_num : (0:ℝ) ≤ (2896375/785398:ℝ))
  calc
    ZeroCount.v1.rvmMain (23171/1000:ℝ) ≤ (2896375/785398:ℝ)*(2039101/1562500:ℝ)-(11585500/3141593:ℝ)+7/8 := by
      unfold ZeroCount.v1.rvmMain
      linarith
    _ ≤ 2 := by norm_num

theorem count_t3 (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (23171/1000:ℝ) ≤ (2:ℝ) :=
  by
    simpa using count_le_of_main_le hsmall (t := 23171/1000) (n := 2)
      (by norm_num) (by norm_num) (by simpa using main_t3)

theorem main_t4 : ZeroCount.v1.rvmMain (27671/1000:ℝ) ≤ (3:ℝ) := by
  have hrhi : (27671/1000:ℝ)/(2*π) ≤ (3458875/785398:ℝ) := by
    have hh : (27671/1000:ℝ)/(2*π) ≤ (27671/1000:ℝ)/(2*(3.141592:ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [pi_gt_d6]
    norm_num at hh ⊢
    exact hh
  have hrlo : (1976500/448799:ℝ) ≤ (27671/1000:ℝ)/(2*π) := by
    have hh : (27671/1000:ℝ)/(2*(3.141593:ℝ)) ≤ (27671/1000:ℝ)/(2*π) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith [pi_lt_d6]
    norm_num at hh ⊢
    exact hh
  have hex : (3458875/785398:ℝ) < exp (18531351/12500000:ℝ) := by
    apply exp_lower_taylor (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl : log ((27671/1000:ℝ)/(2*π)) ≤ (18531351/12500000:ℝ) := by
    apply le_of_lt
    rw [log_lt_iff_lt_exp (by positivity)]
    exact hrhi.trans_lt hex
  have hn : 0 ≤ log ((27671/1000:ℝ)/(2*π)) := by
    apply log_nonneg
    have hh : (1:ℝ) ≤ (1976500/448799:ℝ) := by norm_num
    exact hh.trans hrlo
  have hp := mul_le_mul hrhi hl hn (by norm_num : (0:ℝ) ≤ (3458875/785398:ℝ))
  calc
    ZeroCount.v1.rvmMain (27671/1000:ℝ) ≤ (3458875/785398:ℝ)*(18531351/12500000:ℝ)-(1976500/448799:ℝ)+7/8 := by
      unfold ZeroCount.v1.rvmMain
      linarith
    _ ≤ 3 := by norm_num

theorem count_t4 (hsmall : ZeroCount.v1.rvm_error_small) :
    ZeroCount.v1.zetaNClosed (27671/1000:ℝ) ≤ (3:ℝ) :=
  by
    simpa using count_le_of_main_le hsmall (t := 27671/1000) (n := 3)
      (by norm_num) (by norm_num) (by simpa using main_t4)

theorem log_H_upper : log ((20000:ℝ)/(2*π)) < (8.066:ℝ) := by
  rw [log_lt_iff_lt_exp (by positivity)]
  have hex : (271828/100000:ℝ)^8 ≤ exp 8 := by
    have h1 : (271828/100000:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271828/100000) h1 8
    rw [exp_one_pow] at h2
    exact_mod_cast h2
  have hh := quadratic_le_exp_of_nonneg (show 0 ≤ (0.066:ℝ) by norm_num)
  rw [show (8.066:ℝ) = 8 + 0.066 by norm_num,exp_add]
  calc
    20000/(2*π) ≤ 20000/(2*3.141592:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_d6])
    _ < (271828/100000:ℝ)^8*(1+0.066+0.066^2/2) := by norm_num
    _ ≤ _ := by gcongr

theorem log_t4_lower : (1.482:ℝ) < log ((27671/1000:ℝ)/(2*π)) := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 741/1000)
    (by norm_num : (741/1000:ℝ) ≤ 1) (n := 16) (by norm_num)
  have he : exp (741/1000:ℝ) ≤ (20985/10000:ℝ) := by
    have hh : (∑ i ∈ Finset.range 16, (741/1000:ℝ)^i/(Nat.factorial i:ℝ)) +
      (741/1000:ℝ)^16*(16+1)/(Nat.factorial 16*16) < (20985/10000:ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  have hex : exp (1.482:ℝ) ≤ (20985/10000:ℝ)^2 := by
    rw [show (1.482:ℝ) = 741/1000+741/1000 by norm_num,exp_add]
    nlinarith [Real.exp_pos (741/1000:ℝ)]
  rw [lt_log_iff_exp_lt (by positivity)]
  have hr : (27671/1000:ℝ)/(2*3.141593) ≤ (27671/1000:ℝ)/(2*π) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [pi_lt_d6])
  have hn : (20985/10000:ℝ)^2 < (27671/1000:ℝ)/(2*3.141593) := by norm_num
  exact hex.trans_lt (hn.trans_le hr)

#print axioms count_t4
#print axioms log_t4_lower
end RHContinuation.NumericalZeroLadder
