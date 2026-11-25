/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SameSourceScalar
import IEANTN.Nodes.PrimeInterval.v4.Conclusions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SameSource
open Real Set Finset
noncomputable def P (a b:ℝ):Finset ℕ:=IEANTN.PrimeWindows.primesBetween a b
abbrev Family:=PrimeInterval.v4.optimized_strict_family

lemma log_step {n:ℝ} (hn:0<n) : log (n+1)≤log n+1/n := by
  have h:=log_le_sub_one_of_pos (show 0<(n+1)/n by positivity)
  rw [log_div (by positivity:(n+1:ℝ)≠0) hn.ne'] at h
  have he:(n+1)/n-1=1/n:=by field_simp;ring
  rw [he] at h
  linarith

lemma geometry {n:ℝ} (hn:exp 8≤n) :
    (2000:ℝ)<n ∧ 8≤log n ∧
    3*n^2 < (n+1)^3-n^3 ∧
    (n+1)^3-n^3 ≤ (3003/1000:ℝ)*n^2 ∧
    sqrt ((n+1)^3) ≤ (1001/1000:ℝ)*n*sqrt n ∧
    log ((n+1)^3) ≤ (3001/1000:ℝ)*log n := by
  have hn2:2000<n:=exp8_gt_2000.trans_le hn
  have hn0:0<n:=by linarith
  have hL:8≤log n:=by simpa using log_le_log (exp_pos 8) hn
  have hstep:n+1≤(2001/2000:ℝ)*n:=by linarith
  have hp:=pow_le_pow_left₀ (by positivity:0≤n+1) hstep 3
  have hs:sqrt ((n+1)^3)≤(1001/1000:ℝ)*n*sqrt n:=by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hsn:=sq_sqrt hn0.le
    nlinarith [pow_pos hn0 3]
  have hlstep:=log_le_log (by positivity:0<n+1) hstep
  rw [log_mul (by norm_num:(2001/2000:ℝ)≠0) hn0.ne'] at hlstep
  have hlc:log (2001/2000:ℝ)≤1/2000:=by
    linarith [log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2001/2000)]
  have hl:log ((n+1)^3)≤(3001/1000:ℝ)*log n:=by rw [log_pow];norm_num;linarith
  refine ⟨hn2,hL,by nlinarith,?_,hs,hl⟩
  nlinarith [sq_nonneg (n-2000)]

lemma base_width_gt_one {n:ℝ} (hn:exp 8≤n) :
    (103/100:ℝ) < ((n+1)^3-n^3)/(3*n*sqrt n*log n) := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs2:=sq_sqrt hn0.le
  have hbudget: (27/4:ℝ)*log n < sqrt n := by
    have hL8:8≤log n:=hL
    let u:=log n-8
    have hu:0≤u:=by dsimp [u];linarith
    have ht:=add_one_le_exp (u/2)
    have he:=exp4_gt_54598
    have hp:=mul_lt_mul_of_pos_right he (show 0<1+u/2 by linarith)
    have hp2:=mul_le_mul_of_nonneg_left ht (exp_nonneg 4)
    have hexp:exp (log n/2)=exp 4*exp (u/2):=by rw [←exp_add];congr 1;dsimp [u];ring
    rw [sqrt_exp_log hn0,hexp]
    dsimp [u] at *
    nlinarith
  apply (lt_div_iff₀ (by positivity:0<3*n*sqrt n*log n)).mpr
  have hm:=mul_lt_mul_of_pos_left hbudget (show 0<n*sqrt n by positivity)
  nlinarith

/-- The exact C0<=16 single-window branch of the locked prospective algorithm. -/
theorem single_window_078146 (hf:Family) {n:ℝ} (hn:exp 8≤n)
    (hC:((n+1)^3-n^3)/(3*n*sqrt n*log n)≤16) :
    (39073/50000:ℝ)*n^2/log n < ((P (n^3) ((n+1)^3)).card:ℝ) := by
  obtain ⟨hn2,hL,hΔ,hΔhi,hsb,hlb⟩:=geometry hn
  have hn0:0<n:=by linarith
  have hL0:0<log n:=by linarith
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs2:=sq_sqrt hn0.le
  let C:=((n+1)^3-n^3)/(3*n*sqrt n*log n)
  have hClow:103/100<C:=base_width_gt_one hn
  have hI:C∈Icc (103/100:ℝ) 16:=⟨hClow.le,hC⟩
  have ha:exp 24≤n^3:=by
    have hp:=pow_le_pow_left₀ (exp_nonneg 8) hn 3
    simpa only [←exp_nat_mul,show (3:ℕ)*(8:ℝ)=24 by norm_num] using hp
  have hsqrta:sqrt (n^3)=n*sqrt n:=by rw [show n^3=n^2*n by ring,sqrt_mul (sq_nonneg n),sqrt_sq hn0.le]
  have hloga:log (n^3)=3*log n:=by rw [log_pow];norm_num
  have hwidth:C*sqrt (n^3)*log (n^3)=(n+1)^3-n^3:=by
    rw [hsqrta,hloga]
    dsimp [C]
    field_simp
  have hf':=((hf C hI) (n^3) ha)
  rw [show n^3+C*sqrt (n^3)*log (n^3)=(n+1)^3 by linarith] at hf'
  have heq:((8/9:ℝ)*C-18203/20000+(21/5)/log (n^3))*sqrt (n^3)*log n=
      (8/27:ℝ)*((n+1)^3-n^3)-((18203/20000:ℝ)*log n-7/5)*n*sqrt n:=by
    rw [hsqrta,hloga]
    dsimp [C]
    field_simp
    ring
  have hfl:=mul_lt_mul_of_pos_right hf' hL0
  rw [heq] at hfl
  have hbudget:=error_budget8 hn
  have hcost:=mul_le_mul_of_nonneg_right hbudget (show 0≤n*sqrt n by positivity)
  have hcost':((18203/20000:ℝ)*log n-7/5)*n*sqrt n≤(53859/500000:ℝ)*n^2:=by nlinarith
  have hgoal:(39073/50000:ℝ)*n^2 < ((P (n^3) ((n+1)^3)).card:ℝ)*log n:=by
    by_cases hlate:exp (801/100:ℝ)≤n
    · have hb:=error_budget801 hlate
      have hc:=mul_le_mul_of_nonneg_right hb (show 0≤n*sqrt n by positivity)
      have hc':((18203/20000:ℝ)*log n-7/5)*n*sqrt n≤(107347/1000000:ℝ)*n^2:=by nlinarith
      change _ < ((IEANTN.PrimeWindows.primesBetween (n^3) ((n+1)^3)).card:ℝ)*log n
      nlinarith [sq_pos_of_pos hn0]
    · have hnhi:n<(3012:ℝ):=(lt_of_not_ge hlate).trans exp801_lt_3012
      have hm:=mul_lt_mul_of_pos_left hnhi hn0
      change _ < ((IEANTN.PrimeWindows.primesBetween (n^3) ((n+1)^3)).card:ℝ)*log n
      nlinarith
  exact (div_lt_iff₀ hL0).mpr hgoal
end RH080.SameSource
#print axioms RH080.SameSource.single_window_078146
