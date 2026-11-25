/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ThetaTransport
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.Estimates
open Real Finset

lemma exp8_gt_2000 : (2000 : ℝ) < exp 8 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp14_lt_2000000 : exp 14 < (2000000 : ℝ) := by
  have he : exp 1 ≤ (11 / 4 : ℝ) := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (exp_nonneg 1) he 14
  rw [← exp_nat_mul] at hp
  norm_num at hp
  linarith

lemma exp7_gt_1090 : (1090 : ℝ) < exp 7 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7) 16
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A global, non-sampled logarithm budget for the entire infinite range. -/
lemma log_square_sqrt_budget {n : ℝ} (hn : exp 14 ≤ n) :
    (log n)^2 < (196 / 1090 : ℝ) * sqrt n := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 14 ≤ log n := by simpa using log_le_log (exp_pos 14) hn
  let u := (log n - 14) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht := Real.sum_le_exp_of_nonneg hu 3
  norm_num [Finset.sum_range_succ] at ht
  have hexp : exp (log n / 2) = exp 7 * exp u := by
    rw [← exp_add]
    congr 1
    dsimp [u]
    ring
  have hs : sqrt n = exp (log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [hs, hexp]
  have hprod := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 196)
  have hstrict := mul_lt_mul_of_pos_right exp7_gt_1090 (exp_pos u)
  have hsq := sq_nonneg u
  dsimp [u] at hprod hstrict hsq
  nlinarith

lemma cube_geometry {n : ℝ} (hn : exp 8 ≤ n) :
    (2000 : ℝ) < n ∧ 8 ≤ log n ∧
    sqrt ((n+1)^3) ≤ (1001/1000 : ℝ)*n*sqrt n ∧
    log ((n+1)^3) ≤ (3001/1000 : ℝ)*log n ∧
    0 < log ((n+1)^3) := by
  have hn2 : 2000 < n := exp8_gt_2000.trans_le hn
  have hn0 : 0 < n := by linarith
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  have hstep : n+1 ≤ (2001/2000 : ℝ)*n := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ n+1) hstep 3
  have hs : sqrt ((n+1)^3) ≤ (1001/1000 : ℝ)*n*sqrt n := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hsn := sq_sqrt hn0.le
    nlinarith [pow_pos hn0 3]
  have hlstep := log_le_log (by positivity : 0 < n+1) hstep
  rw [log_mul (by norm_num : (2001/2000 : ℝ) ≠ 0) hn0.ne'] at hlstep
  have hlc : log (2001/2000 : ℝ) ≤ 1/2000 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2001/2000)]
  have hl : log ((n+1)^3) ≤ (3001/1000 : ℝ)*log n := by
    rw [log_pow]
    norm_num
    linarith
  exact ⟨hn2,hL,hs,hl,log_pos (by nlinarith [sq_nonneg n])⟩

/-- The exact source-aware prime count with all endpoint terms exposed. -/
theorem cube_count_schoenfeld_explicit (hS : SchoenfeldTheta61) (hRH : RiemannHypothesis)
    {n : ℝ} (hn : exp 8 ≤ n) :
    (((n+1)^3 - n^3 -
      sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π) -
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π)) /
      log ((n+1)^3) - 1) ≤ ((openPrimes (n^3) ((n+1)^3)).card : ℝ) := by
  have hg := cube_geometry hn
  have hn0 : 0 < n := by linarith [hg.1]
  have ha : (2300000000 : ℝ) ≤ n^3 := by nlinarith [sq_nonneg (n-2000)]
  have hab : n^3 ≤ (n+1)^3 := by nlinarith [sq_nonneg n]
  have hb : (2300000000 : ℝ) ≤ (n+1)^3 := ha.trans hab
  have hsa := (abs_lt.mp (hS hRH (n^3) ha)).2
  have hsb := (abs_lt.mp (hS hRH ((n+1)^3) hb)).1
  apply count_from_theta_bounds (by positivity) hab (by nlinarith [sq_nonneg n])
  · linarith
  · linarith

/-- Finite Büthe range, exploiting the SIGN rather than adding two errors. -/
theorem cube_count_buthe_explicit (hB : ButheTheta1617)
    {n : ℝ} (hn : exp 8 ≤ n) (hhi : n ≤ 2000000) :
    (((n+1)^3-n^3-(39/20 : ℝ)*sqrt ((n+1)^3)) / log ((n+1)^3)-1) ≤
      ((openPrimes (n^3) ((n+1)^3)).card : ℝ) := by
  have hg := cube_geometry hn
  have hn0 : 0 < n := by linarith [hg.1]
  have ha : (1423 : ℝ) ≤ n^3 := by nlinarith [sq_nonneg (n-2000)]
  have hab : n^3 ≤ (n+1)^3 := by nlinarith [sq_nonneg n]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ n+1) (show n+1 ≤ (2000001 : ℝ) by linarith) 3
  have hbmax : (n+1)^3 ≤ (10:ℝ)^19 := by norm_num at hpow ⊢; linarith
  have ha1 : (1:ℝ) ≤ n^3 := by linarith
  have hsa := hB.2 (n^3) ha1 (hab.trans hbmax)
  have hsb := hB.1 ((n+1)^3) (ha.trans hab) hbmax
  have h := count_from_theta_bounds (Ea:=0) (Eb:=(39/20 : ℝ)*sqrt ((n+1)^3))
    (by positivity : 0 ≤ n^3) hab (by nlinarith [sq_nonneg n] : 1 < (n+1)^3)
    (by linarith [sqrt_nonneg (n^3)] : Chebyshev.theta (n^3) ≤ n^3+0) (by linarith)
  simpa using h
lemma exp145_lt_2000000 : exp (29/2 : ℝ) < (2000000 : ℝ) := by
  have he : exp 1 ≤ (27183 / 10000 : ℝ) := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (exp_nonneg 1) he 29
  rw [← exp_nat_mul] at hp
  norm_num at hp
  have hs : (exp (29/2 : ℝ))^2 = exp 29 := by rw [← exp_nat_mul]; norm_num
  have hp0 := exp_pos (29/2 : ℝ)
  nlinarith

lemma exp725_gt_1400 : (1400 : ℝ) < exp (29/4 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 29/4) 18
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma log_square_sqrt_budget145 {n : ℝ} (hn : exp (29/2 : ℝ) ≤ n) :
    (log n)^2 < (841 / 5600 : ℝ) * sqrt n := by
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 29/2 ≤ log n := by simpa using log_le_log (exp_pos (29/2 : ℝ)) hn
  let u := (log n - 29/2) / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht := Real.sum_le_exp_of_nonneg hu 3
  norm_num [Finset.sum_range_succ] at ht
  have hexp : exp (log n / 2) = exp (29/4 : ℝ) * exp u := by
    rw [← exp_add]
    congr 1
    dsimp [u]
    ring
  have hs : sqrt n = exp (log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [hs, hexp]
  have hprod := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 841/4)
  have hstrict := mul_lt_mul_of_pos_right exp725_gt_1400 (exp_pos u)
  have hsq := sq_nonneg u
  dsimp [u] at hprod hstrict hsq
  nlinarith

/-- A global classical RH late-range budget; no sampled real parameters. -/
theorem cube_density_096_late (hS : SchoenfeldTheta61) (hRH : RiemannHypothesis)
    {n : ℝ} (hn : exp (29/2 : ℝ) ≤ n) :
    (24/25 : ℝ)*n^2/log n < ((openPrimes (n^3) ((n+1)^3)).card : ℝ) := by
  have hn8 : exp 8 ≤ n := (exp_le_exp.mpr (by norm_num : (8:ℝ) ≤ 29/2)).trans hn
  have hg := cube_geometry hn8
  have hn2 : 2000 < n := hg.1
  have hn0 : 0 < n := by linarith
  have hL : 8 ≤ log n := hg.2.1
  have hL0 : 0 < log n := by linarith
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs2 := sq_sqrt hn0.le
  have hlogb0 := hg.2.2.2.2
  have hgeomlog := hg.2.2.2.1
  have hgeomsqrt := hg.2.2.1
  have hlogb : log ((n+1)^3) = 3*log (n+1) := by rw [log_pow]; norm_num
  have hloga : log (n^3) = 3*log n := by rw [log_pow]; norm_num
  have hsqrta : sqrt (n^3) = n*sqrt n := by
    rw [show n^3=n^2*n by ring, sqrt_mul (sq_nonneg n), sqrt_sq hn0.le]
  have hlogmon : log n ≤ log (n+1) := log_le_log hn0 (by linarith)
  have hsa : (2300000000:ℝ) ≤ n^3 := by nlinarith [sq_nonneg (n-2000)]
  have hab : n^3 ≤ (n+1)^3 := by nlinarith [sq_nonneg n]
  have hS₁ := (abs_lt.mp (hS hRH (n^3) hsa)).2
  have hS₂ := (abs_lt.mp (hS hRH ((n+1)^3) (hsa.trans hab))).1
  have hpi : 0 < 8*π := by positivity
  have hA : sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π) ≤
      (3/8:ℝ)*n*sqrt n*(log n)^2 := by
    rw [hsqrta,hloga]
    apply (div_le_iff₀ hpi).mpr
    have hp := mul_lt_mul_of_pos_left Real.pi_gt_three (by positivity : 0 < n*sqrt n*(log n)^2)
    nlinarith [mul_nonneg (by positivity : 0 ≤ n*sqrt n) (by linarith : 0 ≤ log n)]
  have hB : sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π) ≤
      (377/1000:ℝ)*n*sqrt n*(log n)^2 := by
    apply (div_le_iff₀ hpi).mpr
    have h1 : (log ((n+1)^3)-2)*log ((n+1)^3) ≤
        ((3001/1000:ℝ)*log n)^2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sqrt_nonneg ((n+1)^3))
    have h3 := mul_le_mul_of_nonneg_right hgeomsqrt (sq_nonneg ((3001/1000:ℝ)*log n))
    have hp := mul_lt_mul_of_pos_left Real.pi_gt_three (by positivity : 0 < n*sqrt n*(log n)^2)
    have hx : 0 < n*sqrt n*(log n)^2 := by positivity
    nlinarith only [h2,h3,hp,hx]
  have hbudget := log_square_sqrt_budget145 hn
  have hbudget' := mul_lt_mul_of_pos_left hbudget (show 0 < n*sqrt n by positivity)
  have hbudget2 : (752/1000:ℝ)*n*sqrt n*(log n)^2 < (113/1000:ℝ)*n^2 := by
    nlinarith
  have hnlog : log n ≤ n-1 := log_le_sub_one_of_pos hn0
  have hbig : (3001/1000:ℝ)*log n < (1/500:ℝ)*n^2 := by nlinarith [sq_nonneg (n-2000)]
  have hcount := theta_sub_le_open_count (by positivity : 0 ≤ n^3) hab (by nlinarith [sq_nonneg n] : 1 ≤ (n+1)^3)
  have hweight : ((24/25:ℝ)*n^2/log n)*log ((n+1)^3) ≤ (24/25:ℝ)*(3001/1000)*n^2 := by
    have hm := mul_le_mul_of_nonneg_left hgeomlog (by positivity : 0 ≤ (24/25:ℝ)*n^2/log n)
    calc
      _ ≤ ((24/25:ℝ)*n^2/log n)*((3001/1000:ℝ)*log n) := hm
      _ = _ := by field_simp
  by_contra hno
  have hc : ((openPrimes (n^3) ((n+1)^3)).card:ℝ) ≤ (24/25:ℝ)*n^2/log n := le_of_not_gt hno
  have hm := mul_le_mul_of_nonneg_right hc hlogb0.le
  nlinarith [sq_nonneg n]

/-- The literature finite numerical estimate closes every real point before the
late analytic budget; the two sources remain visible assumptions. -/
theorem cube_density_096 (hB : ButheTheta1617) (hS : SchoenfeldTheta61)
    (hRH : RiemannHypothesis) {n : ℝ} (hn : exp 8 ≤ n) :
    (24/25 : ℝ)*n^2/log n < ((openPrimes (n^3) ((n+1)^3)).card : ℝ) := by
  by_cases hlate : exp (29/2 : ℝ) ≤ n
  · exact cube_density_096_late hS hRH hlate
  have hhi : n ≤ 2000000 := (le_of_not_ge hlate).trans (exp145_lt_2000000.le)
  have hg := cube_geometry hn
  have hn0 : 0 < n := by linarith [hg.1]
  have hL0 : 0 < log n := by linarith [hg.2.1]
  have hs2 := sq_sqrt hn0.le
  have hs0 : 0 < sqrt n := sqrt_pos.mpr hn0
  have hs40 : 40 < sqrt n := by nlinarith [hg.1]
  have hlogb0 := hg.2.2.2.2
  have hgeomlog := hg.2.2.2.1
  have hgeomsqrt := hg.2.2.1
  have hcount := cube_count_buthe_explicit hB hn hhi
  have hmul := (div_le_iff₀ hlogb0).mp ((sub_le_iff_le_add).mp hcount)
  have hnlog : log n ≤ n-1 := log_le_sub_one_of_pos hn0
  have hcost : (39/20:ℝ)*sqrt ((n+1)^3) < (1/20:ℝ)*n^2 := by
    have hm := mul_lt_mul_of_pos_left (show (39/20:ℝ)*(1001/1000) < (1/20:ℝ)*sqrt n by linarith) (show 0 < n*sqrt n by positivity)
    nlinarith
  have hsmall : log ((n+1)^3) < (1/500:ℝ)*n^2 := by nlinarith [hg.1,sq_nonneg (n-2000)]
  have hweight : ((24/25:ℝ)*n^2/log n)*log ((n+1)^3) ≤ (24/25:ℝ)*(3001/1000)*n^2 := by
    have hm := mul_le_mul_of_nonneg_left hgeomlog (by positivity : 0 ≤ (24/25:ℝ)*n^2/log n)
    calc
      _ ≤ ((24/25:ℝ)*n^2/log n)*((3001/1000:ℝ)*log n) := hm
      _ = _ := by field_simp
  by_contra hno
  have hc : ((openPrimes (n^3) ((n+1)^3)).card:ℝ) ≤ (24/25:ℝ)*n^2/log n := le_of_not_gt hno
  have hm := mul_le_mul_of_nonneg_right hc hlogb0.le
  nlinarith [sq_nonneg n]

end RH080.Estimates
#print axioms RH080.Estimates.cube_count_schoenfeld_explicit
#print axioms RH080.Estimates.cube_count_buthe_explicit
