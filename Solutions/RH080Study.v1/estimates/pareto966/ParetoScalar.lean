/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeEnvelopes
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.Pareto966
open Real Finset

lemma exp_upper_anchor (x M : ℝ) (hx : 0 ≤ x)
    (hq : M < (27182818283/10000000000:ℝ)^14 *
      (∑ k ∈ Finset.range 14, x^k/(Nat.factorial k:ℝ))) : M < exp (14+x) := by
  have he : (27182818283/10000000000:ℝ) ≤ exp 1 := (by norm_num : (27182818283/10000000000:ℝ)≤2.7182818283).trans Real.exp_one_gt_d9.le
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27182818283/10000000000) he 14
  rw [←exp_nat_mul] at hp
  simp only [Nat.cast_ofNat, mul_one] at hp
  have ht := Real.sum_le_exp_of_nonneg hx 14
  have hpos : 0≤∑ k ∈ Finset.range 14, x^k/(Nat.factorial k:ℝ) := by positivity
  rw [exp_add]
  exact hq.trans_le (mul_le_mul hp ht hpos (exp_nonneg 14))

lemma log_anchor1 : log (2154433:ℝ) < (72915191/5000000:ℝ) := by
  apply (log_lt_iff_lt_exp (by norm_num : (0:ℝ)<2154433)).mpr
  have h:=exp_upper_anchor (2915191/5000000:ℝ) 2154433 (by norm_num) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

lemma log_anchor2 : log (2160000:ℝ) < (14585619/1000000:ℝ) := by
  apply (log_lt_iff_lt_exp (by norm_num : (0:ℝ)<2160000)).mpr
  have h:=exp_upper_anchor (585619/1000000:ℝ) 2160000 (by norm_num) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

/-- A quadratic/exponential comparison on the complete real ray, not a scan. -/
lemma polynomial_budget {M U r a n:ℝ} (hM:0<M) (hr:0<r) (hrM:r^2<M)
    (hU:8≤U) (ha:0≤a) (ha1:a≤1) (hlog:log M<U) (hn:M≤n)
    (hL:8≤log n) :
    (log n)^2-a*log n < ((U^2-a*U)/r)*sqrt n := by
  have hn0:0<n:=hM.trans_le hn
  have hPu:0<U^2-a*U:=by nlinarith
  have hnS:r<sqrt n:=by nlinarith [sq_sqrt hn0.le,sqrt_nonneg n]
  by_cases hLU:log n≤U
  · have hm:=mul_nonneg (show 0≤U-log n by linarith) (show 0≤U+log n-a by linarith)
    have hs:=mul_lt_mul_of_pos_left hnS (show 0<(U^2-a*U)/r by positivity)
    have hid:((U^2-a*U)/r)*r=U^2-a*U:=by field_simp
    nlinarith
  · have hUL:U≤log n:=le_of_not_ge hLU
    let u:ℝ:=(log n-U)/2
    have hu:0≤u:=by dsimp [u];linarith
    have ht:=Real.sum_le_exp_of_nonneg hu 3
    norm_num [Finset.sum_range_succ] at ht
    have hpoly:(log n)^2-a*log n≤(U^2-a*U)*(1+u+u^2/2):=by
      have hq:0≤(U^2-a*U)/2-4:=by nlinarith
      have hl:0≤U^2-a*U-4*U+2*a:=by nlinarith
      have h1:=mul_nonneg hq (sq_nonneg u)
      have h2:=mul_nonneg hl hu
      dsimp [u] at *
      nlinarith
    have hMu:M<exp U:=(log_lt_iff_lt_exp hM).mp hlog
    have hEU:r<exp (U/2):=by
      have hid:(exp (U/2))^2=exp U:=by rw [←exp_nat_mul];congr 1;ring
      nlinarith [exp_pos (U/2)]
    have hroot:sqrt n=exp (U/2)*exp u:=by
      rw [←exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hn0]
      congr 1
      dsimp [u];ring
    have ht2:=mul_le_mul_of_nonneg_left ht hPu.le
    have hs:=mul_lt_mul_of_pos_right hEU (exp_pos u)
    rw [←hroot] at hs
    have ht3:=mul_lt_mul_of_pos_left hs (show 0<(U^2-a*U)/r by positivity)
    have hid:((U^2-a*U)/r)*(r*exp u)=(U^2-a*U)*exp u:=by field_simp
    rw [hid] at ht3
    exact hpoly.trans_lt (ht2.trans_lt ht3)

lemma seam_budget {n:ℝ} (hn:(2154433:ℝ)≤n) (hL:8≤log n) :
    (1+1/(2154433:ℝ))*(3*log n+3/2154433-2)*log n <
      (33007996/1000000000:ℝ)*(4*π)*sqrt n := by
  have hp:=polynomial_budget (M:=2154433) (U:=72915191/5000000)
    (r:=14677986919/10000000) (a:=2/3-1/2154433) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) log_anchor1 hn hL
  have hi:(31415926535/10000000000:ℝ)<π:=lt_trans (by norm_num) pi_gt_d20
  have hp2:=mul_lt_mul_of_pos_left hp (by norm_num : (0:ℝ)<3*(1+1/(2154433:ℝ)))
  have hs:0<sqrt n:=sqrt_pos.mpr (by linarith)
  have hi2:=mul_lt_mul_of_pos_right hi hs
  nlinarith only [hp2,hi2,hs]

lemma late_budget {n:ℝ} (hn:(2160000:ℝ)≤n) (hL:8≤log n) :
    (1+1/(2160000:ℝ))*(3*log n+3/2160000-2)*log n <
      (33/1000:ℝ)*(4*π)*sqrt n := by
  have hp:=polynomial_budget (M:=2160000) (U:=14585619/1000000)
    (r:=1469693845/1000000) (a:=2/3-1/2160000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) log_anchor2 hn hL
  have hi:(31415926535/10000000000:ℝ)<π:=lt_trans (by norm_num) pi_gt_d20
  have hp2:=mul_lt_mul_of_pos_left hp (by norm_num : (0:ℝ)<3*(1+1/(2160000:ℝ)))
  have hs:0<sqrt n:=sqrt_pos.mpr (by linarith)
  have hi2:=mul_lt_mul_of_pos_right hi hs
  nlinarith only [hp2,hi2,hs]
end RH080.Pareto966
#print axioms RH080.Pareto966.seam_budget
#print axioms RH080.Pareto966.late_budget
