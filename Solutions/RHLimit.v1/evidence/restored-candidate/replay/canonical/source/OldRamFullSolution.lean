/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v3.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import ActualFinalProfile

namespace RamanujanGap.v3
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

lemma fullEnvelope_eq (l : ℝ) :
    fullEnvelope l = dynamicBase l-Ramanujan640.RHTail.D Ramanujan640.RHTail.a l := by
  unfold fullEnvelope dynamicBase
  rw [sourcePolynomial_eq]
  rfl

lemma profile_eq (x : ℝ) : profile x = finalMargin x := by
  unfold profile finalMargin
  simp only [fullEnvelope_eq]

lemma normalized_to_gap {x B : ℝ} (hx : 1 < x) (h : B ≤ RamStudy.RG x) :
    B*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos hx
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(B*x^2/(log x)^6)=B := by
    field_simp [hx0.ne',hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact h

theorem challenge_one_twelfth_margin (hRH : RH.v1.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi) : one_twelfth_margin := by
  intro x hx
  apply normalized_to_gap (by linarith : 1 < x)
  exact source_ramanujan_640b hRH hT hJ hL hU hS hx

theorem challenge_tail_144_margin (hRH : RH.v1.hypothesis)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi) : tail_144_margin := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 70) hx
  have hl : (70:ℝ) ≤ log x := by
    apply exp_le_exp.mp
    simpa only [exp_log hx0] using hx
  apply normalized_to_gap (one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 70) |>.trans_le hx)
  simpa only [exp_log hx0] using actual_tail_144 hRH hS hl

theorem challenge_full_profile (hRH : RH.v1.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi) : full_profile := by
  intro x hx
  rw [profile_eq]
  exact final_gap_profile hRH hT hJ hL hU hS hx

theorem challenge_ramanujan (hRH : RH.v1.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi) : ramanujan := by
  intro x hx
  have h := challenge_one_twelfth_margin hRH hT hJ hL hU hS x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith : 1 < x)
  have hp : 0 < (1/12:ℝ)*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms challenge_one_twelfth_margin
#print axioms challenge_tail_144_margin
#print axioms challenge_full_profile
#print axioms challenge_ramanujan
end RamanujanGap.v3
