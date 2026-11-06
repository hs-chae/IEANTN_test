/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Common
import DirectIntervalA.SourcePairing

namespace DirectIntervalA
open Real Set MeasureTheory Complex WinnerDirectKernel
set_option maxHeartbeats 0

/-- The large-height count needs only the all-height RvM source premise. -/
theorem closed_count_le_mul_log (hrvm : ZeroCount.v1.rvm_error_bound)
    {t : ℝ} (ht : 3*(10:ℝ)^12 ≤ t) :
    ZeroCount.v1.zetaNClosed t ≤ t*Real.log t := by
  have ht12 : 12 ≤ t := by norm_num at ht; linarith
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t := by
    rw [←Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hpi := Real.pi_gt_three
  have hd0 : 0 ≤ t/(2*Real.pi) := by positivity
  have hd : t/(2*Real.pi) ≤ t/2 := by
    exact div_le_div_of_nonneg_left ht0.le (by norm_num) (by linarith)
  have hlog : Real.log (t/(2*Real.pi)) ≤ Real.log t := by
    apply Real.log_le_log (by positivity)
    exact div_le_self ht0.le (by linarith)
  have hprod := mul_le_mul_of_nonneg_left hlog hd0
  have hprod2 := mul_le_mul_of_nonneg_right hd (show 0 ≤ Real.log t by linarith)
  have hgap := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ t/2-1/5 by linarith)
  have hn := CH2Section7Z.zetaN_le hrvm (by linarith : 1 ≤ t)
  unfold ZeroCount.v1.rvmMain at hn
  nlinarith

/-- A finite actual-zero subset has no larger cumulative count. -/
theorem subset_rvm_count (hrvm : ZeroCount.v1.rvm_error_bound)
    (S : Finset ℂ) {V t : ℝ}
    (hS : ∀ rho ∈ S, rho ∈ positiveZeros V)
    (ht : 3*(10:ℝ)^12 ≤ t) :
    (∑ rho ∈ S, if rho.im ≤ t then (IEANTN.zetaOrder rho : ℝ) else 0) ≤
      t*Real.log t := by
  classical
  apply le_trans ?_ (closed_count_le_mul_log hrvm ht)
  rw [ZeroCount.v1.zetaNClosed,
    CH2Section7Z.zetaZeroesSum_eq_sum
      (CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=t) le_rfl)]
  simp only [one_mul]
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hmem,hcut⟩ := Finset.mem_filter.mp hr
    have hm := positive_mem (hS rho hmem)
    exact (Set.Finite.mem_toFinset _).mpr ⟨trivial,⟨hm.2.1.1,hcut⟩,hm.2.2⟩
  · intro rho hr _
    have hm := (Set.Finite.mem_toFinset _).mp hr
    exact CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm

theorem delta_pos (L : ℝ) : 0 < delta L := Real.exp_pos _

theorem delta_le_hundredth {L : ℝ} (hL : 330 ≤ L) : delta L ≤ 1/100 := by
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ L/5 by linarith)
  have hsq : (66:ℝ)^2 ≤ (L/5)^2 := by nlinarith
  have hbig : (100:ℝ) ≤ Real.exp (L/5) := by nlinarith
  unfold delta
  rw [show -L/5=-(L/5) by ring,Real.exp_neg]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<100) hbig)

theorem delta_le_one {L : ℝ} (hL : 330 ≤ L) : delta L ≤ 1 :=
  (delta_le_hundredth hL).trans (by norm_num)

theorem two_add_delta_le_k {L : ℝ} (hL : 330 ≤ L) : 2+delta L ≤ k := by
  have hd := delta_le_hundredth hL
  norm_num [k] at *
  linarith

theorem U_ge_height {L : ℝ} (hL : 330 ≤ L) : 3*(10:ℝ)^12 ≤ U L := by
  have he := Real.pow_div_factorial_le_exp (66:ℝ) (by norm_num) 12
  norm_num at he
  have h66 : Real.exp 66 ≤ Real.exp (L/5) := Real.exp_le_exp.mpr (by linarith)
  unfold U
  norm_num [k]
  nlinarith

theorem U_le_V {L : ℝ} (hL : 330 ≤ L) : U L ≤ V L := by
  have he := Real.exp_pos (L/5)
  unfold U V truncHeight
  have hc : k ≤ 240*L := by norm_num [k]; linarith
  nlinarith

theorem truncHeight_lower {L : ℝ} (hL : 330 ≤ L) :
    max 51 (L^2) < truncHeight L := by
  have he := Real.add_one_le_exp (L/5)
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 120*L by linarith)
  unfold truncHeight
  apply max_lt_iff.mpr
  constructor <;> nlinarith [sq_nonneg L]

theorem exp_three_tenths_large {L : ℝ} (hL : 330 ≤ L) :
    480*L+2 < Real.exp (3*L/10) := by
  have hs : (108900:ℝ) ≤ L^2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hs (show 0≤L by linarith)
  have he := Real.pow_div_factorial_le_exp (3*L/10) (show 0≤3*L/10 by linarith) 3
  norm_num at he
  nlinarith

theorem truncHeight_upper {L : ℝ} (hL : 330 ≤ L) :
    truncHeight L < (Real.sqrt (Real.exp L)-2)/4 := by
  have he := Real.exp_pos (L/5)
  have he1 : 1 ≤ Real.exp (L/5) := Real.one_le_exp_iff.mpr (by linarith)
  have hb := mul_lt_mul_of_pos_right (exp_three_tenths_large hL) he
  have heq : Real.exp (3*L/10)*Real.exp (L/5)=Real.exp (L/2) := by
    rw [←Real.exp_add];congr 1;ring
  rw [heq] at hb
  rw [←Real.exp_half]
  unfold truncHeight
  nlinarith

theorem truncation_domain {L : ℝ} (hL : 330 ≤ L) :
    max 51 (Real.log (Real.exp L)^2) < truncHeight L ∧
      truncHeight L < (Real.sqrt (Real.exp L)-2)/4 := by
  rw [Real.log_exp]
  exact ⟨truncHeight_lower hL,truncHeight_upper hL⟩

theorem gap_ratio (L : ℝ) : Real.exp (4*L/5)/Real.exp L=delta L := by
  rw [←Real.exp_sub]
  unfold delta
  congr 1
  ring

#print axioms subset_rvm_count
#print axioms truncation_domain
end DirectIntervalA
