/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SameSource
open Real Finset

lemma exp8_gt_2000 : (2000:ℝ)<exp 8 := by
  have h:=sum_le_exp_of_nonneg (by norm_num:(0:ℝ)≤8) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp4_gt_54598 : (5459813/100000:ℝ)<exp 4 := by
  have h:=sum_le_exp_of_nonneg (by norm_num:(0:ℝ)≤4) 18
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp4005_gt_54871 : (548718/10000:ℝ)<exp (801/200:ℝ) := by
  have h:=sum_le_exp_of_nonneg (by norm_num:(0:ℝ)≤801/200) 18
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp801_lt_3012 : exp (801/100:ℝ)<(3012:ℝ) := by
  have he:exp 1≤(27182818286/10000000000:ℝ):=Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp:=pow_le_pow_left₀ (exp_nonneg 1) he 8
  rw [←exp_nat_mul] at hp
  norm_num at hp
  have hsmall:=exp_bound_div_one_sub_of_interval (by norm_num:(0:ℝ)≤1/100)
    (by norm_num:(1/100:ℝ)<1)
  have hid:exp (801/100:ℝ)=exp 8*exp (1/100:ℝ):=by rw [←exp_add];norm_num
  rw [hid]
  have hm:=mul_le_mul hp hsmall (exp_nonneg (1/100:ℝ)) (by norm_num)
  norm_num at hm
  linarith

lemma sqrt_exp_log {n:ℝ} (hn:0<n) : sqrt n=exp (log n/2) := by
  rw [sqrt_eq_rpow,rpow_def_of_pos hn]
  congr 1
  ring

/-- The exponential tangent controls every point of a full infinite real ray. -/
lemma affine_log_error_budget {n L0 K:ℝ} (hn:0<n) (hL: L0≤log n)
    (hL0:8≤L0) (hK:0<K)
    (hstart:(18203/20000:ℝ)*L0-7/5≤K*exp (L0/2)) :
    (18203/20000:ℝ)*log n-7/5≤K*sqrt n := by
  let u:=log n-L0
  have hu:0≤u:=by dsimp [u];linarith
  have ht:=add_one_le_exp (u/2)
  have hbasepos:0<(18203/20000:ℝ)*L0-7/5:=by linarith
  have hprod:=mul_le_mul_of_nonneg_right hstart (show 0≤1+u/2 by linarith)
  have hprod2:=mul_le_mul_of_nonneg_left ht (show 0≤K*exp (L0/2) by positivity)
  have hexp:exp (log n/2)=exp (L0/2)*exp (u/2):=by
    rw [←exp_add]
    congr 1
    dsimp [u]
    ring
  rw [sqrt_exp_log hn,hexp]
  have hpoly: (18203/20000:ℝ)*log n-7/5≤
      ((18203/20000:ℝ)*L0-7/5)*(1+u/2):=by
    have hm:=mul_nonneg hu (show 0≤((18203/20000:ℝ)*L0-7/5)/2-18203/20000 by linarith)
    dsimp [u] at *
    nlinarith only [hm]
  nlinarith only [hpoly,hprod,hprod2]

lemma error_budget8 {n:ℝ} (hn:exp 8≤n) :
    (18203/20000:ℝ)*log n-7/5≤(53859/500000:ℝ)*sqrt n := by
  have hn0:0<n:=(exp_pos _).trans_le hn
  apply affine_log_error_budget hn0 (by simpa using log_le_log (exp_pos 8) hn)
    (by norm_num:(8:ℝ)≤8) (by norm_num)
  norm_num
  nlinarith [exp4_gt_54598]

lemma error_budget801 {n:ℝ} (hn:exp (801/100:ℝ)≤n) :
    (18203/20000:ℝ)*log n-7/5≤(107347/1000000:ℝ)*sqrt n := by
  have hn0:0<n:=(exp_pos _).trans_le hn
  apply affine_log_error_budget hn0 (by simpa using log_le_log (exp_pos (801/100:ℝ)) hn)
    (by norm_num:(8:ℝ)≤801/100) (by norm_num)
  norm_num
  nlinarith [exp4005_gt_54871]

lemma log_div_sqrt_budget12 {n:ℝ} (hn:exp 12≤n) :
    log n < (3/100:ℝ)*sqrt n := by
  have hn0:0<n:=(exp_pos _).trans_le hn
  have hL:12≤log n:=by simpa using log_le_log (exp_pos 12) hn
  let u:=log n-12
  have hu:0≤u:=by dsimp [u];linarith
  have he: (400:ℝ)<exp 6:=by
    have h:=sum_le_exp_of_nonneg (by norm_num:(0:ℝ)≤6) 15
    norm_num [Finset.sum_range_succ] at h
    linarith
  have ht:=add_one_le_exp (u/2)
  have hm:=mul_lt_mul_of_pos_right he (show 0<1+u/2 by linarith)
  have hm2:=mul_le_mul_of_nonneg_left ht (exp_nonneg 6)
  have hexp:exp (log n/2)=exp 6*exp (u/2):=by rw [←exp_add];congr 1;dsimp [u];ring
  rw [sqrt_exp_log hn0,hexp]
  dsimp [u] at *
  nlinarith
end RH080.SameSource
#print axioms RH080.SameSource.error_budget8
#print axioms RH080.SameSource.error_budget801
#print axioms RH080.SameSource.log_div_sqrt_budget12
