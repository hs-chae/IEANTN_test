/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroSource
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

private theorem log_upper_fraction (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    log x ≤ 2*(x-1)/(x+1) := by
  have hy : 0 ≤ 1/x-1 := by apply sub_nonneg.mpr; exact (one_le_div hx).mpr hx1
  have h := Real.le_log_one_add_of_nonneg hy
  rw [show 1+(1/x-1) = 1/x by ring,log_div one_ne_zero hx.ne',log_one] at h
  have he : 2*(1/x-1)/(1/x-1+2) = 2*(1-x)/(1+x) := by
    rw [show 1/x-1+2 = (1+x)/x by field_simp <;> ring]
    field_simp [hx.ne',show 1+x ≠ 0 by positivity]
    <;> ring
  rw [he] at h
  calc
    log x ≤ -(2*(1-x)/(1+x)) := by linarith
    _ = 2*(x-1)/(x+1) := by ring

private theorem cmsQ_nine_neg : cmsQ 9 < 0 := by
  let y : ℝ := 9/(2*π*exp 1)
  have hy : 0 < y := by dsimp [y]; positivity
  have hprod := mul_le_mul pi_gt_d2.le
    (show (271/100:ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) (by norm_num : (0:ℝ)≤271/100) pi_pos.le
  have hycap : y ≤ (53/100:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*π*exp 1)).mpr
    nlinarith
  have hl := (Real.log_le_log hy hycap).trans (log_upper_fraction (53/100) (by norm_num) (by norm_num))
  norm_num at hl
  have hc : (10/7:ℝ) ≤ 9/(2*π) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*π)).mpr
    linarith [pi_lt_d2]
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ)≤9/(2*π))
  have hn := mul_le_mul_of_nonpos_right hc (by norm_num : (-94/153:ℝ)≤0)
  unfold cmsQ
  change (9/(2*π))*log y+7/8 < 0
  linarith

private theorem cmsQ_ten_pos : 0 < cmsQ 10 := by
  let z : ℝ := π/5
  have hz : 0 < z := by dsimp [z]; positivity
  have hzlo : (157/250:ℝ) ≤ z := by dsimp [z]; linarith [pi_gt_d2]
  have hzhi : z ≤ (63/100:ℝ) := by dsimp [z]; linarith [pi_lt_d2]
  have hs : (157/250:ℝ)^2 ≤ z^2 := pow_le_pow_left₀ (by norm_num) hzlo 2
  have hfrac : 2*(z-1)/(z+1) < (7/8:ℝ)*z-1 := by
    apply (div_lt_iff₀ (by positivity : 0 < z+1)).mpr
    nlinarith
  have hl : log z < (7/8:ℝ)*z-1 :=
    (log_upper_fraction z hz (by linarith)).trans_lt hfrac
  have hquot : (log z+1)/z < (7/8:ℝ) := (div_lt_iff₀ hz).mpr (by linarith)
  have heq : cmsQ 10 = -(log z+1)/z+7/8 := by
    unfold cmsQ
    have harg : 10/(2*π*exp 1) = (1/z)/(exp 1) := by dsimp [z]; field_simp <;> ring
    rw [harg,log_div (by positivity : (1/z:ℝ)≠0) (exp_ne_zero 1),
      log_div one_ne_zero hz.ne',log_one,log_exp]
    dsimp [z]
    field_simp
    <;> ring
  rw [heq,neg_div]
  linarith

/-- Certified existence of the exact CMS comparison root in (9,10), by
rational pi/exponential inequalities and the intermediate value theorem.
The displayed approximation 9.676... is never supplied as an oracle. -/
theorem cms_zero_count_root_exists : SourceCMSZeroCountRoot := by
  have hcont : ContinuousOn cmsQ (Icc (9:ℝ) 10) := by
    intro T hT
    have hT0 : T ≠ 0 := by have h := hT.1; linarith
    have hden : (2*π*exp 1:ℝ) ≠ 0 := by positivity
    have harg : T/(2*π*exp 1) ≠ 0 := div_ne_zero hT0 hden
    unfold cmsQ
    fun_prop
  obtain ⟨T0,hT0,hQ⟩ := intermediate_value_Icc (by norm_num : (9:ℝ)≤10) hcont
    (show (0:ℝ) ∈ Icc (cmsQ 9) (cmsQ 10) from ⟨cmsQ_nine_neg.le,cmsQ_ten_pos.le⟩)
  have hT09 : 9 < T0 := by
    by_contra hh
    have heq : T0 = 9 := le_antisymm (le_of_not_gt hh) hT0.1
    rw [heq] at hQ
    linarith [cmsQ_nine_neg]
  have hT010 : T0 < 10 := by
    by_contra hh
    have heq : T0 = 10 := le_antisymm hT0.2 (le_of_not_gt hh)
    rw [heq] at hQ
    linarith [cmsQ_ten_pos]
  exact ⟨T0,by linarith [exp_one_lt_three],hT09,hT010,hQ⟩

#print axioms cms_zero_count_root_exists
end RH080Next.Explicit
