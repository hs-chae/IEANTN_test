/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeEnvelopes
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.Estimates
open Real Finset
lemma log_refined_sqrt_budget {n : ℝ} (hn : exp (29/2 : ℝ) ≤ n) :
    (log n)^2-(33/50:ℝ)*log n < (10034/70000:ℝ)*sqrt n := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 29/2 ≤ log n := by simpa using log_le_log (exp_pos (29/2 : ℝ)) hn
  let u := (log n - 29/2) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht := Real.sum_le_exp_of_nonneg hu 3
  norm_num [Finset.sum_range_succ] at ht
  have hexp : exp (log n / 2) = exp (29/4:ℝ)*exp u := by
    rw [←exp_add];congr 1;dsimp [u];ring
  have hs : sqrt n = exp (log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0];congr 1;ring
  rw [hs,hexp]
  have hprod := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 5017/25)
  have hstrict := mul_lt_mul_of_pos_right exp725_gt_1400 (exp_pos u)
  have hsq := sq_nonneg u
  dsimp [u] at hprod hstrict hsq
  nlinarith

theorem cube_density_0965_late (hS : SchoenfeldTheta61) (hRH : RiemannHypothesis)
    {n : ℝ} (hn : exp (29/2 : ℝ) ≤ n) :
    (193/200:ℝ)*n^2/log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  have hn8 : exp 8 ≤ n := (exp_le_exp.mpr (by norm_num : (8:ℝ) ≤ 29/2)).trans hn
  have hg := cube_geometry hn8
  have hn0 : 0 < n := by linarith [hg.1]
  have hL : 29/2 ≤ log n := by simpa using log_le_log (exp_pos (29/2:ℝ)) hn
  have hL0 : 0 < log n := by linarith
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs2 := sq_sqrt hn0.le
  have hn10 : (10000:ℝ) < n := by
    have he7 := exp7_gt_1090
    have he14 : exp 14 = (exp 7)^2 := by rw [←exp_nat_mul];norm_num
    have he14n : exp 14 ≤ n := (exp_le_exp.mpr (by norm_num : (14:ℝ) ≤ 29/2)).trans hn
    nlinarith
  have hlogb0 := hg.2.2.2.2
  have hgeomlog := hg.2.2.2.1
  have hgeomsqrt := hg.2.2.1
  have hloga : log (n^3)=3*log n := by rw [log_pow];norm_num
  have hlogmon : 3*log n ≤ log ((n+1)^3) := by
    rw [log_pow];norm_num;linarith [log_le_log hn0 (show n≤n+1 by linarith)]
  have hsqrta : sqrt (n^3)=n*sqrt n := by
    rw [show n^3=n^2*n by ring,sqrt_mul (sq_nonneg n),sqrt_sq hn0.le]
  have hsa : (2300000000:ℝ) ≤ n^3 := by nlinarith [sq_nonneg (n-2000)]
  have hab : n^3 ≤ (n+1)^3 := by nlinarith [sq_nonneg n]
  have hS₁ := (abs_lt.mp (hS hRH (n^3) hsa)).2
  have hS₂ := (abs_lt.mp (hS hRH ((n+1)^3) (hsa.trans hab))).1
  have hpi : 0 < 8*π := by positivity
  have htot : sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π) ≤
      (359/500:ℝ)*n*sqrt n*((log n)^2-(33/50:ℝ)*log n) := by
    rw [←add_div,hsqrta,hloga]
    apply (div_le_iff₀ hpi).mpr
    have h1 : (log ((n+1)^3)-2)*log ((n+1)^3) ≤
        ((3001/1000:ℝ)*log n-2)*((3001/1000:ℝ)*log n) := by
      have ht : 0 ≤ (3001/1000:ℝ)*log n-log ((n+1)^3) := by linarith
      have hv : 0 ≤ (3001/1000:ℝ)*log n+log ((n+1)^3)-2 := by linarith
      nlinarith [mul_nonneg ht hv]
    have h2 := mul_le_mul_of_nonneg_left h1 (sqrt_nonneg ((n+1)^3))
    have h3 := mul_le_mul_of_nonneg_right hgeomsqrt
      (mul_nonneg (show 0 ≤ (3001/1000:ℝ)*log n-2 by linarith)
        (by positivity : 0 ≤ (3001/1000:ℝ)*log n))
    have hx : 0 < n*sqrt n*((log n)^2-(33/50:ℝ)*log n) := by
      apply mul_pos (by positivity)
      nlinarith
    have hpx := mul_lt_mul_of_pos_left Real.pi_gt_d2 hx
    have hX : 0 < n*sqrt n*log n := by positivity
    have hX2 : 0 < n*sqrt n*(log n)^2 := by positivity
    nlinarith only [h2,h3,hpx,hX,hX2]
  have hbudget := log_refined_sqrt_budget hn
  have hbudget' := mul_lt_mul_of_pos_left hbudget (show 0 < n*sqrt n by positivity)
  have hbudget2 : (359/500:ℝ)*n*sqrt n*((log n)^2-(33/50:ℝ)*log n) <
      (103/1000:ℝ)*n^2 := by nlinarith
  have hnlog : log n ≤ n-1 := log_le_sub_one_of_pos hn0
  have hbig : log ((n+1)^3) < (1/1000:ℝ)*n^2 := by
    nlinarith [sq_nonneg (n-10000)]
  have hcount := theta_sub_le_open_count (by positivity : 0 ≤ n^3) hab
    (by nlinarith [sq_nonneg n] : 1 ≤ (n+1)^3)
  have hweight : ((193/200:ℝ)*n^2/log n)*log ((n+1)^3) ≤
      (193/200:ℝ)*(3001/1000)*n^2 := by
    have hm := mul_le_mul_of_nonneg_left hgeomlog (by positivity : 0 ≤ (193/200:ℝ)*n^2/log n)
    calc
      _ ≤ ((193/200:ℝ)*n^2/log n)*((3001/1000:ℝ)*log n) := hm
      _ = _ := by field_simp
  by_contra hno
  have hc : ((openPrimes (n^3) ((n+1)^3)).card:ℝ) ≤ (193/200:ℝ)*n^2/log n := le_of_not_gt hno
  have hm := mul_le_mul_of_nonneg_right hc hlogb0.le
  nlinarith [sq_nonneg n]
lemma exp6_gt_400 : (400:ℝ) < exp 6 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 15
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma cube_geometry6 {n : ℝ} (hn : exp 6 ≤ n) :
    (400:ℝ) < n ∧ 6 ≤ log n ∧
    sqrt ((n+1)^3) ≤ (251/250:ℝ)*n*sqrt n ∧
    log ((n+1)^3) ≤ (1501/500:ℝ)*log n ∧ 0 < log ((n+1)^3) := by
  have hn4 : 400 < n := exp6_gt_400.trans_le hn
  have hn0 : 0 < n := by linarith
  have hL : 6 ≤ log n := by simpa using log_le_log (exp_pos 6) hn
  have hstep : n+1 ≤ (401/400:ℝ)*n := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ n+1) hstep 3
  have hs : sqrt ((n+1)^3) ≤ (251/250:ℝ)*n*sqrt n := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hsn := sq_sqrt hn0.le
    nlinarith [pow_pos hn0 3]
  have hlstep := log_le_log (by positivity : 0 < n+1) hstep
  rw [log_mul (by norm_num : (401/400:ℝ) ≠ 0) hn0.ne'] at hlstep
  have hlc : log (401/400:ℝ) ≤ 1/400 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 401/400)]
  have hl : log ((n+1)^3) ≤ (1501/500:ℝ)*log n := by
    rw [log_pow];norm_num;linarith
  exact ⟨hn4,hL,hs,hl,log_pos (by nlinarith [sq_nonneg n])⟩

theorem cube_density_0965_finite (hB : ButheTheta1617)
    {n : ℝ} (hn : exp 6 ≤ n) (hhi : n ≤ 2000000) :
    (193/200:ℝ)*n^2/log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  have hg := cube_geometry6 hn
  have hn4 : 400 < n := hg.1
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < log n := by linarith [hg.2.1]
  have hs2 := sq_sqrt hn0.le
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs20 : 20 < sqrt n := by nlinarith
  have hlogb0 := hg.2.2.2.2
  have hgeomlog := hg.2.2.2.1
  have hgeomsqrt := hg.2.2.1
  have ha : (1423:ℝ) ≤ n^3 := by nlinarith [sq_nonneg (n-400)]
  have hab : n^3 ≤ (n+1)^3 := by nlinarith [sq_nonneg n]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ n+1) (show n+1 ≤ (2000001:ℝ) by linarith) 3
  have hbmax : (n+1)^3 ≤ (10:ℝ)^19 := by norm_num at hpow ⊢;linarith
  have hsa := hB.2 (n^3) (by linarith : (1:ℝ) ≤ n^3) (hab.trans hbmax)
  have hsb := hB.1 ((n+1)^3) (ha.trans hab) hbmax
  have hcount := theta_sub_le_open_count (by positivity : 0 ≤ n^3) hab
    (by nlinarith [sq_nonneg n] : 1 ≤ (n+1)^3)
  have hupper : Chebyshev.theta (n^3) < n^3 := by linarith [sqrt_nonneg (n^3)]
  have hcost : (39/20:ℝ)*sqrt ((n+1)^3) < (49/500:ℝ)*n^2 := by
    have hm := mul_lt_mul_of_pos_left
      (show (39/20:ℝ)*(251/250) < (49/500:ℝ)*sqrt n by linarith)
      (show 0 < n*sqrt n by positivity)
    nlinarith
  have hloghalf : log n ≤ n/2 := by
    have h := log_le_sub_one_of_pos (show 0 < n/2 by positivity)
    rw [log_div hn0.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hsmall : log ((n+1)^3) < (1/250:ℝ)*n^2 := by
    nlinarith [sq_nonneg (n-400)]
  have hweight : ((193/200:ℝ)*n^2/log n)*log ((n+1)^3) ≤
      (193/200:ℝ)*(1501/500)*n^2 := by
    have hm := mul_le_mul_of_nonneg_left hgeomlog (by positivity : 0 ≤ (193/200:ℝ)*n^2/log n)
    calc
      _ ≤ ((193/200:ℝ)*n^2/log n)*((1501/500:ℝ)*log n) := hm
      _ = _ := by field_simp
  by_contra hno
  have hc : ((openPrimes (n^3) ((n+1)^3)).card:ℝ) ≤ (193/200:ℝ)*n^2/log n := le_of_not_gt hno
  have hm := mul_le_mul_of_nonneg_right hc hlogb0.le
  nlinarith [sq_nonneg n]

/-- Stronger coefficient AND earlier real onset. The finite-range source remains
unconditional literature input, the infinite range additionally uses ordinary RH. -/
theorem cube_density_0965 (hB : ButheTheta1617) (hS : SchoenfeldTheta61)
    (hRH : RiemannHypothesis) {n : ℝ} (hn : exp 6 ≤ n) :
    (193/200:ℝ)*n^2/log n < ((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  by_cases hlate : exp (29/2:ℝ) ≤ n
  · exact cube_density_0965_late hS hRH hlate
  · exact cube_density_0965_finite hB hn ((le_of_not_ge hlate).trans exp145_lt_2000000.le)

end RH080.Estimates
#print axioms RH080.Estimates.cube_density_0965_late

#print axioms RH080.Estimates.cube_density_0965_finite
#print axioms RH080.Estimates.cube_density_0965
