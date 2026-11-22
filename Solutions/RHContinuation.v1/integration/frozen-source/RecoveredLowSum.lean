/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ZeroCountIntegral
open Real Set MeasureTheory
namespace RHContinuation.RecoveredLowSum
open CH2Section7Z RHContinuation.DiscreteZeroCount
  RHContinuation.NumericalZeroLadder RHContinuation.ZeroCountIntegral
set_option maxHeartbeats 2000000

private theorem main_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c d : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (ZeroCount.v1.rvmMain t+c*log t+d)/t^2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hne (t : ℝ) (ht : t ∈ uIcc a b) : t ≠ 0 := by
    rw [uIcc_of_le hab] at ht
    exact ne_of_gt (ha.trans_le ht.1)
  have hm : ContinuousOn ZeroCount.v1.rvmMain (uIcc a b) := by
    unfold ZeroCount.v1.rvmMain
    exact (((continuousOn_id.div_const (2*π)).mul
      ((continuousOn_id.div_const (2*π)).log
        (fun t ht => div_ne_zero (hne t ht) (by positivity)))).sub
      (continuousOn_id.div_const (2*π))).add continuousOn_const
  exact ((hm.add (continuousOn_const.mul (continuousOn_id.log hne))).add
    continuousOn_const).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (hne t ht))

private theorem cell_bound {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : ZeroCount.v1.zetaNClosed b ≤ c) :
    (∫ t in a..b, ZeroCount.v1.zetaNClosed t/t^2) ≤ c*(1/a-1/b) := by
  have hcont : ContinuousOn (fun t : ℝ => c/t^2) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1))
  rw [← integral_const_eval ha hab c]
  apply intervalIntegral.integral_mono_on hab
    (count_div_sq_integrable ha hab) hcont.intervalIntegrable
  intro t ht
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  exact (count_mono (ha.le.trans ht.1) ht.2).trans hc

/-- The four integer count cells retain the actual low-count staircase. -/
theorem integral_low_cells (hsmall : ZeroCount.v1.rvm_error_small) :
    (∫ t in (2*π)..(27671/1000:ℝ), ZeroCount.v1.zetaNClosed t/t^2) ≤
      1/(9676/1000:ℝ)+1/(17847/1000:ℝ)+1/(23171/1000:ℝ)-3/(27671/1000:ℝ) := by
  have h0 : 0 < (2*π:ℝ) := by positivity
  have h01 : (2*π:ℝ) ≤ 9676/1000 := by linarith [pi_lt_four]
  have h1 := cell_bound h0 h01 (count_t1 hsmall)
  have h2 := cell_bound (a := 9676/1000) (b := 17847/1000)
    (by norm_num) (by norm_num) (count_t2 hsmall)
  have h3 := cell_bound (a := 17847/1000) (b := 23171/1000)
    (by norm_num) (by norm_num) (count_t3 hsmall)
  have h4 := cell_bound (a := 23171/1000) (b := 27671/1000)
    (by norm_num) (by norm_num) (count_t4 hsmall)
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (count_div_sq_integrable h0 h01)
    (count_div_sq_integrable (a := 9676/1000) (b := 17847/1000)
      (by norm_num) (by norm_num))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (count_div_sq_integrable h0 (show (2*π:ℝ) ≤ 17847/1000 by linarith [pi_lt_four]))
    (count_div_sq_integrable (a := 17847/1000) (b := 23171/1000)
      (by norm_num) (by norm_num))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals
    (count_div_sq_integrable h0 (show (2*π:ℝ) ≤ 23171/1000 by linarith [pi_lt_four]))
    (count_div_sq_integrable (a := 23171/1000) (b := 27671/1000)
      (by norm_num) (by norm_num))
  norm_num at h1 h2 h3 h4 ⊢
  linarith

/-- No inverse-ordinate database: two unchanged published zero-count predicates
suffice, after recovering the integer staircase instead of its real envelope. -/
theorem recovered_cap (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small) :
    2*IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000)
      (fun ρ : ℂ => 1/ρ.im) < (10.5:ℝ) := by
  let c : ℝ := 27671/1000
  let b : ℝ := 280
  let H : ℝ := 20000
  have hc : 0 < c := by norm_num [c]
  have hcb : c ≤ b := by norm_num [c,b]
  have hbH : b ≤ H := by norm_num [b,H]
  have hb : 0 < b := by norm_num [b]
  have hH : 0 < H := by norm_num [H]
  have hlow := integral_low_cells hsmall
  have hmid : (∫ t in c..b, ZeroCount.v1.zetaNClosed t/t^2) ≤
      primitive 0 1 b - primitive 0 1 c := by
    rw [← integral_main_eval hc hcb 0 1]
    apply intervalIntegral.integral_mono_on hcb
      (count_div_sq_integrable hc hcb) (main_integrable hc hcb 0 1)
    intro t ht
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    have hh := (abs_lt.mp (hsmall t (hc.trans_le ht.1)
      (by dsimp [b] at ht;exact ht.2))).2
    simp only [zero_mul,add_zero]
    linarith
  have hhigh : (∫ t in b..H, ZeroCount.v1.zetaNClosed t/t^2) ≤
      primitive (1/5) 2 H - primitive (1/5) 2 b := by
    rw [← integral_main_eval hb hbH (1/5) 2]
    apply intervalIntegral.integral_mono_on hbH
      (count_div_sq_integrable hb hbH) (main_integrable hb hbH (1/5) 2)
    intro t ht
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    have hh := (abs_le.mp (hrvm t (by dsimp [b] at ht; linarith [ht.1]))).2
    linarith
  have hend : ZeroCount.v1.zetaNClosed H/H ≤
      (ZeroCount.v1.rvmMain H+log H/5+2)/H := by
    apply div_le_div_of_nonneg_right _ hH.le
    have hh := (abs_le.mp (hrvm H (by norm_num [H]))).2
    linarith
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (count_div_sq_integrable (a := 2*π) (b := c) (by positivity)
      (by dsimp [c];linarith [pi_lt_four])) (count_div_sq_integrable hc hcb)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (count_div_sq_integrable (a := 2*π) (b := b) (by positivity)
      (by dsimp [b];linarith [pi_lt_four])) (count_div_sq_integrable hb hbH)
  have hexact := reciprocal_identity hsmall
  let U : ℝ := (ZeroCount.v1.rvmMain H+log H/5+2)/H +
    (1/(9676/1000:ℝ)+1/(17847/1000:ℝ)+1/(23171/1000:ℝ)-3/c) +
    (primitive 0 1 b-primitive 0 1 c) +
    (primitive (1/5) 2 H-primitive (1/5) 2 b)
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000)
      (fun ρ : ℂ => 1/ρ.im) ≤ U := by
    dsimp only [U,c,b,H] at hmid hhigh hend hs1 hs2 ⊢
    linarith
  have hU : U =
      1/(9676/1000:ℝ)+1/(17847/1000:ℝ)+1/(23171/1000:ℝ) +
      (ZeroCount.v1.rvmMain c-2)/c +
      (log (H/(2*π))^2-log (c/(2*π))^2)/(4*π) +
      (log b/5+6/5)/b - 1/(5*H) := by
    dsimp [U,primitive]
    unfold ZeroCount.v1.rvmMain
    field_simp [ne_of_gt hc,ne_of_gt hb,ne_of_gt hH,pi_ne_zero]
    ring
  have hmc : ZeroCount.v1.rvmMain c ≤ (3:ℝ) := main_t4
  have hcl : 0 ≤ log (c/(2*π)) := by
    have hh := log_t4_lower
    dsimp [c]
    linarith
  have hHl : 0 ≤ log (H/(2*π)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    dsimp [H]
    linarith [pi_lt_four]
  have hlogsq : log (H/(2*π))^2-log (c/(2*π))^2 ≤
      (8.066:ℝ)^2-(1.482:ℝ)^2 := by
    have hh := log_H_upper
    have hc' := log_t4_lower
    change log (H/(2*π)) < (8.066:ℝ) at hh
    change (1.482:ℝ) < log (c/(2*π)) at hc'
    nlinarith
  have hmainterm : (log (H/(2*π))^2-log (c/(2*π))^2)/(4*π) ≤
      ((8.066:ℝ)^2-(1.482:ℝ)^2)/(4*3.141592) := by
    apply le_trans (div_le_div_of_nonneg_right hlogsq (by positivity))
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [pi_gt_d6]
  have hlogb : log b ≤ (6:ℝ) := by
    rw [log_le_iff_le_exp hb]
    have hh : (7:ℝ) ≤ exp 2 := by
      have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      linarith
    have h1 := pow_le_pow_left₀ (show (0:ℝ) ≤ 7 by norm_num) hh 3
    rw [← Real.exp_nat_mul] at h1
    norm_num at h1
    dsimp [b]
    linarith
  have hcfrac : (ZeroCount.v1.rvmMain c-2)/c ≤ 1/c := by
    apply (div_le_div_iff_of_pos_right hc).mpr
    linarith
  have hbfrac : (log b/5+6/5)/b ≤ (6/5+6/5)/b := by
    apply div_le_div_of_nonneg_right _ hb.le
    linarith
  have hfinal : (2:ℝ) *
      (1/(9676/1000:ℝ)+1/(17847/1000:ℝ)+1/(23171/1000:ℝ)+1/c +
      (((8.066:ℝ)^2-(1.482:ℝ)^2)/(4*3.141592)) + (6/5+6/5)/b - 1/(5*H)) <
      (10.5:ℝ) := by norm_num [c,b,H]
  linarith

#print axioms recovered_cap
end RHContinuation.RecoveredLowSum
