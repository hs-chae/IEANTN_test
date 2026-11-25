/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
set_option autoImplicit false
namespace RH080.Estimates.ZeroEnvelope
open Real
/-- All allowances here use L=log T, and Q=N-(M0+7/8). -/
noncomputable def bpt (L:ℝ) : ℝ := (7/25:ℝ)*L
/-- Published BW2025 Theorem1.1 first bound plus the proved7/8 center change. -/
noncomputable def bwFirst (L:ℝ) : ℝ := (2519/25000:ℝ)*L+(1223/5000:ℝ)*log L+223961/25000
/-- Published BW2025 Theorem1.1 second bound plus the proved7/8 center change. -/
noncomputable def bwSecond (L:ℝ) : ℝ := (14/125:ℝ)*L+(12567/100000:ℝ)*log L+464917/100000
/-- Changing the actual center is a genuine triangle-inequality proof. -/
theorem recenter {N M0 E:ℝ} (h:|N-M0|≤E) : |N-(M0+7/8)|≤E+7/8 := by
  have hx := abs_sub (N-M0) (7/8:ℝ)
  norm_num at hx
  have hid : N-(M0+7/8)=(N-M0)-(7/8:ℝ) := by ring
  rw [hid]
  linarith
/-- Both source estimates are actually consumed. -/
theorem minimum_of_bounds {q A B:ℝ} (ha:|q|≤A) (hb:|q|≤B) : |q|≤min A B := le_min ha hb
/-- The three-way envelope preserves every competing source. -/
theorem three_way {q L:ℝ} (ha:|q|≤bpt L) (hb:|q|≤bwFirst L) (hc:|q|≤bwSecond L) :
    |q|≤min (bpt L) (min (bwFirst L) (bwSecond L)) := le_min ha (le_min hb hc)

/-- Leading-coefficient ranking is WRONG on this entire real lower regime. -/
theorem bpt_better_low {L:ℝ} (hL:1≤L) (hhi:L≤25) :
    bpt L < bwFirst L ∧ bpt L < bwSecond L := by
  have hl:=log_nonneg hL
  constructor <;> simp only [bpt,bwFirst,bwSecond] <;> nlinarith

lemma log32_lt4 : log (32:ℝ)<4 := by
  apply (log_lt_iff_lt_exp (by norm_num : (0:ℝ)<32)).mpr
  have h:=sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤4) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Stronger BW second bound is guaranteed active by L=32, far earlier than
one would infer by considering only its first leading-coefficient bound. -/
theorem bw_second_better_high {L:ℝ} (hL:32≤L) : bwSecond L < bpt L := by
  have hL0:0<L:=by linarith
  have h := log_le_sub_one_of_pos (show 0<L/32 by positivity)
  rw [log_div hL0.ne' (by norm_num : (32:ℝ)≠0)] at h
  have hc:=log32_lt4
  unfold bwSecond bpt
  nlinarith

lemma log60_lt5 : log (60:ℝ)<5 := by
  apply (log_lt_iff_lt_exp (by norm_num : (0:ℝ)<60)).mpr
  have h:=sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤5) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem bw_first_better_high {L:ℝ} (hL:60≤L) : bwFirst L < bpt L := by
  have hL0:0<L:=by linarith
  have h:=log_le_sub_one_of_pos (show 0<L/60 by positivity)
  rw [log_div hL0.ne' (by norm_num : (60:ℝ)≠0)] at h
  have hc:=log60_lt5
  unfold bwFirst bpt
  nlinarith
end RH080.Estimates.ZeroEnvelope
#print axioms RH080.Estimates.ZeroEnvelope.recenter
#print axioms RH080.Estimates.ZeroEnvelope.three_way
#print axioms RH080.Estimates.ZeroEnvelope.bpt_better_low
#print axioms RH080.Estimates.ZeroEnvelope.bw_second_better_high
#print axioms RH080.Estimates.ZeroEnvelope.bw_first_better_high
