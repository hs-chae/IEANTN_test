/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.Explicit

private def expUpper (x : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, x^j/(j.factorial:ℝ))+x^n*((n+1:ℕ):ℝ)/((n.factorial:ℝ)*n)

private def expLower (x : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, x^j/(j.factorial:ℝ))-x^n*((n+1:ℕ):ℝ)/((n.factorial:ℝ)*n)

private theorem exp_le_upper (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n) :
    exp x ≤ expUpper x n := by
  simpa only [expUpper,Nat.cast_add,Nat.cast_one] using Real.exp_bound' hx hx1 hn

private theorem lower_le_exp (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hn : 0 < n) :
    expLower x n ≤ exp x := by
  have hh : |x| ≤ 1 := by rw [abs_of_nonneg hx]; exact hx1
  have h := Real.exp_bound hh hn
  rw [abs_of_nonneg hx] at h
  have heq : x^n*((n+1:ℕ):ℝ)/((n.factorial:ℝ)*n) = x^n*(((n+1:ℕ):ℝ)/((n.factorial:ℝ)*n)) := by ring
  unfold expLower
  rw [heq]
  have hb := (abs_sub_le_iff.mp h).2
  linarith

/-- Kernel analytic bounds for the fixed signed-moment cutoff. These use
proved real Taylor remainders; they are not external numerical outputs or PV. -/
theorem log_three_eighths_bounds :
    -(9809/10000:ℝ) ≤ log (3/8:ℝ) ∧ log (3/8:ℝ) ≤ -(613/625:ℝ) := by
  have hu := exp_le_upper (613/625) 12 (by norm_num) (by norm_num) (by norm_num)
  have huR : expUpper (613/625) 12 ≤ (8/3:ℝ) := by norm_num [expUpper,Finset.sum_range_succ]
  have hl := lower_le_exp (9809/10000) 10 (by norm_num) (by norm_num) (by norm_num)
  have hlR : (8/3:ℝ) ≤ expLower (9809/10000) 10 := by norm_num [expLower,Finset.sum_range_succ]
  have hloglo : (613/625:ℝ) ≤ log (8/3:ℝ) := (le_log_iff_exp_le (by norm_num)).mpr (hu.trans huR)
  have hloghi : log (8/3:ℝ) ≤ (9809/10000:ℝ) := (log_le_iff_le_exp (by norm_num)).mpr (hlR.trans hl)
  rw [show (3/8:ℝ) = (8/3:ℝ)⁻¹ by norm_num,log_inv]
  constructor <;> linarith

theorem log_sixteen_upper : log (16:ℝ) ≤ (13863/5000:ℝ) := by
  have hl := lower_le_exp (13863/20000) 12 (by norm_num) (by norm_num) (by norm_num)
  have hlR : (2:ℝ) ≤ expLower (13863/20000) 12 := by norm_num [expLower,Finset.sum_range_succ]
  have hlog : log (2:ℝ) ≤ (13863/20000:ℝ) := (log_le_iff_le_exp (by norm_num)).mpr (hlR.trans hl)
  rw [show (16:ℝ) = (2:ℝ)^4 by norm_num,log_pow]
  norm_num
  linarith

private theorem exp_four_upper : exp (4:ℝ) ≤ (27183/10000:ℝ)^4 := by
  have he : exp 1 ≤ (27183/10000:ℝ) := by linarith [exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 4
  rw [←exp_nat_mul] at hp
  norm_num at hp ⊢
  exact hp

theorem log_slab_right_lower : (42427/10000:ℝ) ≤ log (348/5:ℝ) := by
  have hf := exp_le_upper (2427/10000) 6 (by norm_num) (by norm_num) (by norm_num)
  have hm := mul_le_mul exp_four_upper hf (exp_pos _).le
    (by positivity : (0:ℝ)≤(27183/10000:ℝ)^4)
  have heq : exp 4*exp (2427/10000) = exp (42427/10000:ℝ) := by rw [←exp_add]; norm_num
  rw [heq] at hm
  have hr : (27183/10000:ℝ)^4*expUpper (2427/10000) 6 ≤ (348/5:ℝ) := by
    norm_num [expUpper,Finset.sum_range_succ]
  exact (le_log_iff_exp_le (by norm_num)).mpr (hm.trans hr)

theorem log_slab_left_lower : (2:ℝ) ≤ log (84/5:ℝ) := by
  have he : exp 1 ≤ (27183/10000:ℝ) := by linarith [exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 2
  rw [←exp_nat_mul] at hp
  norm_num at hp
  have hr : (738915489/100000000:ℝ) ≤ (84/5:ℝ) := by norm_num
  exact (le_log_iff_exp_le (by norm_num)).mpr (hp.trans hr)

theorem two_le_log_of_fifteen_le (x : ℝ) (hx : 15 ≤ x) : (2:ℝ) ≤ log x := by
  have he : exp 1 ≤ (27183/10000:ℝ) := by linarith [exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 2
  rw [←exp_nat_mul] at hp
  norm_num at hp
  have hr : (738915489/100000000:ℝ) ≤ x := by linarith
  exact (le_log_iff_exp_le (by linarith : 0 < x)).mpr (hp.trans hr)

private theorem exp_three_upper : exp (3:ℝ) ≤ (27183/10000:ℝ)^3 := by
  have he : exp 1 ≤ (27183/10000:ℝ) := by linarith [exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 3
  rw [←exp_nat_mul] at hp
  norm_num at hp ⊢
  exact hp

theorem log_074_right_lower : (157/50:ℝ) ≤ log (2331/100:ℝ) := by
  have hf := exp_le_upper (7/50) 4 (by norm_num) (by norm_num) (by norm_num)
  have hm := mul_le_mul exp_three_upper hf (exp_pos _).le (by positivity : (0:ℝ)≤(27183/10000:ℝ)^3)
  have heq : exp 3*exp (7/50) = exp (157/50:ℝ) := by rw [←exp_add]; norm_num
  rw [heq] at hm
  have hr : (27183/10000:ℝ)^3*expUpper (7/50) 4 ≤ (2331/100:ℝ) := by norm_num [expUpper,Finset.sum_range_succ]
  exact (le_log_iff_exp_le (by norm_num)).mpr (hm.trans hr)

theorem log_075_right_lower : (16/5:ℝ) ≤ log (105/4:ℝ) := by
  have hf := exp_le_upper (1/5) 4 (by norm_num) (by norm_num) (by norm_num)
  have hm := mul_le_mul exp_three_upper hf (exp_pos _).le (by positivity : (0:ℝ)≤(27183/10000:ℝ)^3)
  have heq : exp 3*exp (1/5) = exp (16/5:ℝ) := by rw [←exp_add]; norm_num
  rw [heq] at hm
  have hr : (27183/10000:ℝ)^3*expUpper (1/5) 4 ≤ (105/4:ℝ) := by norm_num [expUpper,Finset.sum_range_succ]
  exact (le_log_iff_exp_le (by norm_num)).mpr (hm.trans hr)

#print axioms log_three_eighths_bounds
#print axioms log_sixteen_upper
#print axioms log_slab_right_lower
end RH080Next.Explicit
