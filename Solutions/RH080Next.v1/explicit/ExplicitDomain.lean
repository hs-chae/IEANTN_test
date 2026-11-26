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

def intervalRatio (c t : ℝ) : ℝ := c*t*exp (-t/2)
def halfLogWidth (c t : ℝ) : ℝ := log (1+intervalRatio c t)/2

theorem polynomial_exp_decay (t : ℝ) (ht : 42 ≤ t) (k : ℕ)
    (hk : 1 ≤ k) (hk42 : 2*(k:ℝ) ≤ 42) :
    t^k*exp (-t/2) ≤ 42^k*exp (-21) := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hbase : t/42 ≤ exp ((t-42)/(2*k)) := by
    have h := Real.add_one_le_exp ((t-42)/(2*k))
    have hr : t/42 ≤ (t-42)/(2*k)+1 := by
      have hd : 0 < 2*(k:ℝ) := by positivity
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<42)).mpr
      have heq := div_mul_cancel₀ (t-42) hd.ne'
      have hp := mul_nonneg (div_nonneg (sub_nonneg.mpr ht) hd.le) (sub_nonneg.mpr hk42)
      nlinarith
    exact hr.trans h
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ t/42) hbase k
  have he : exp ((t-42)/(2*k))^k = exp ((t-42)/2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    <;> ring
  rw [he, div_pow] at hp
  have hmul := mul_le_mul_of_nonneg_right hp (le_of_lt (exp_pos (-t/2)))
  have hexp : exp ((t-42)/2)*exp (-t/2) = exp (-21) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hexp] at hmul
  have hden : 0 < (42:ℝ)^k := by positivity
  have hf : (t^k*exp (-t/2))/(42:ℝ)^k ≤ exp (-21) := by
    simpa only [div_mul_eq_mul_div] using hmul
  simpa only [mul_comm] using (div_le_iff₀ hden).mp hf

theorem exp_twenty_one_lower : (1050000000:ℝ) < exp 21 := by
  have he : (27/10:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0:ℝ) ≤ 27/10) (by norm_num : (21:ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem exp_neg_twenty_one_upper : exp (-21) < (1/1050000000:ℝ) := by
  rw [exp_neg]
  simpa only [one_div] using (inv_lt_inv₀ (exp_pos 21) (by norm_num)).mpr exp_twenty_one_lower

theorem intervalRatio_pos (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (ht : 42 ≤ t) :
    0 < intervalRatio c t := by unfold intervalRatio; positivity

theorem intervalRatio_upper (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) : intervalRatio c t < (40/1000000000:ℝ) := by
  have hp := polynomial_exp_decay t ht 1 (by norm_num) (by norm_num)
  have he := exp_neg_twenty_one_upper
  unfold intervalRatio
  have hct : c*t ≤ t := mul_le_of_le_one_left (by linarith) hc1
  have hz := mul_le_mul_of_nonneg_right hct (le_of_lt (exp_pos (-t/2)))
  norm_num at hp
  nlinarith

theorem halfLogWidth_bounds (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) : 0 < halfLogWidth c t ∧ halfLogWidth c t < (20/1000000000:ℝ) := by
  have hz := intervalRatio_pos c t hc ht
  have hzu := intervalRatio_upper c t hc hc1 ht
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+intervalRatio c t)
  unfold halfLogWidth
  constructor
  · exact div_pos (Real.log_pos (by linarith)) (by norm_num)
  · linarith

/-- The spectral support envelope lies well above x/2. This includes R=7;
there is no inherited support-six restriction. -/
theorem support_lower_geometry (c t R : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) (hR : R ≤ 10) :
    exp t/2 < exp (t+(1-R)*halfLogWidth c t) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hl : -(1/2:ℝ) < (1-R)*halfLogWidth c t := by nlinarith
  have he := Real.add_one_le_exp ((1-R)*halfLogWidth c t)
  have he' : (1/2:ℝ) < exp ((1-R)*halfLogWidth c t) := by linarith
  rw [exp_add]
  nlinarith [exp_pos t]

/-- A support-seven mollification by radius at most one stays in the same
fixed compact positive arithmetic interval throughout the limiting process. -/
theorem mollifier_support_geometry (c t ε : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 < exp (t+((1:ℝ)-8)*halfLogWidth c t) ∧
      Set.Icc (exp (t+(1-(7+ε))*halfLogWidth c t))
        (exp (t+(1+(7+ε))*halfLogWidth c t)) ⊆
      Set.Icc (exp (t+((1:ℝ)-8)*halfLogWidth c t))
        (exp (t+((1:ℝ)+8)*halfLogWidth c t)) := by
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hl := support_lower_geometry c t 8 hc hc1 ht (by norm_num)
  have he : (2:ℝ) < exp t := Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr (by linarith))
  refine ⟨lt_trans (by linarith : 1 < exp t/2) hl, ?_⟩
  intro y hy
  constructor
  · exact (Real.exp_le_exp.mpr (by nlinarith)).trans hy.1
  · exact hy.2.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- The finite integer envelope does not depend on the mollifier radius. -/
theorem finite_arithmetic_envelope (b : ℝ) :
    {n : ℕ | (n:ℝ) ≤ b}.Finite := by
  apply (Set.finite_Iic (⌈b⌉₊)).subset
  intro n hn
  have h : (n:ℝ) ≤ (⌈b⌉₊:ℝ) := hn.trans (Nat.le_ceil b)
  exact_mod_cast h

/-- The actual optimized log-domain parameters give positive-frequency
support for every radius used in the original explicit experiments. -/
theorem mellin_positive_frequency_domain (c t R : ℝ)
    (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t) (hR : R ≤ 10) :
    R*halfLogWidth c t < t+halfLogWidth c t := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hm := mul_le_mul_of_nonneg_right hR hd.1.le
  nlinarith

end RH080Next.Explicit
