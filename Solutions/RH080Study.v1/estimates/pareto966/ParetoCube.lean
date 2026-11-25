/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ParetoTransfer
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.Pareto966
open Real Finset RH080.Estimates

/-- The original finite Büthe range covers the entire real cube up to the
fixed seam. This deliberately loose .98 lemma needs no new source input. -/
theorem finite_098 (hB:ButheTheta1617) {n:ℝ} (hn:exp 8≤n) (hhi:n≤2154433) :
    (49/50:ℝ)*n^2/log n<((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  have hg:=cube_geometry hn
  have hn0:0<n:=by linarith [hg.1]
  have hL0:0<log n:=by linarith [hg.2.1]
  have hs2:=sq_sqrt hn0.le
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs40:40<sqrt n:=by nlinarith [hg.1]
  have hb0:=hg.2.2.2.2
  have ha:(1423:ℝ)≤n^3:=by nlinarith [sq_nonneg (n-2000),hg.1]
  have hab:n^3≤(n+1)^3:=by nlinarith [sq_nonneg n]
  have hp:=pow_le_pow_left₀ (by positivity : 0≤n+1) (show n+1≤(2154434:ℝ) by linarith) 3
  have hbmax:(n+1)^3≤(10:ℝ)^19:=by norm_num at hp ⊢;linarith
  have hsa:=hB.2 (n^3) (by linarith : (1:ℝ)≤n^3) (hab.trans hbmax)
  have hsb:=hB.1 ((n+1)^3) (ha.trans hab) hbmax
  have hcount:=theta_sub_le_open_count (by positivity : 0≤n^3) hab
    (by nlinarith [sq_nonneg n] : 1≤(n+1)^3)
  have hu:Chebyshev.theta (n^3)≤n^3:=by linarith [sqrt_nonneg (n^3)]
  have hcost:(39/20:ℝ)*sqrt ((n+1)^3)<(1/20:ℝ)*n^2:=by
    have hm:=mul_lt_mul_of_pos_left
      (show (39/20:ℝ)*(1001/1000)<(1/20:ℝ)*sqrt n by linarith)
      (show 0<n*sqrt n by positivity)
    nlinarith [hg.2.2.1]
  have hlog:log n≤n-1:=log_le_sub_one_of_pos hn0
  have hsmall:log ((n+1)^3)<(1/500:ℝ)*n^2:=by
    nlinarith [hg.1,hg.2.2.2.1,sq_nonneg (n-2000)]
  have hweight:((49/50:ℝ)*n^2/log n)*log ((n+1)^3)≤(49/50:ℝ)*(3001/1000)*n^2:=by
    have hm:=mul_le_mul_of_nonneg_left hg.2.2.2.1 (by positivity : 0≤(49/50:ℝ)*n^2/log n)
    calc
      _≤((49/50:ℝ)*n^2/log n)*((3001/1000:ℝ)*log n):=hm
      _=_:=by field_simp
  by_contra hno
  have hc:((openPrimes (n^3) ((n+1)^3)).card:ℝ)≤(49/50:ℝ)*n^2/log n:=le_of_not_gt hno
  have hm:=mul_le_mul_of_nonneg_right hc hb0.le
  nlinarith [sq_nonneg n]

lemma endpoint_allowance {n:ℝ} (hn:(2154433:ℝ)≤n) :
    1<(1/1000000000:ℝ)*n^2/log n := by
  have hn0:0<n:=by linarith
  have hL0:0<log n:=log_pos (by linarith)
  have hs0:0<sqrt n:=sqrt_pos.mpr hn0
  have hs2:=sq_sqrt hn0.le
  have hs1000:(1000:ℝ)<sqrt n:=by nlinarith
  have hbig:(2000000000:ℝ)<n*sqrt n:=by
    nlinarith [mul_pos (show 0<n-2000000 by linarith) (show 0<sqrt n-1000 by linarith)]
  have hm:=mul_lt_mul_of_pos_right hbig hs0
  have hid:(n*sqrt n)*sqrt n=n^2:=by rw [mul_assoc,←pow_two,sq_sqrt hn0.le];ring
  rw [hid] at hm
  have hl:=log_le_sub_one_of_pos hs0
  rw [log_sqrt hn0.le] at hl
  apply (lt_div_iff₀ hL0).mpr
  nlinarith

/-- Same two source inputs and fixed seam as the frozen written discovery.
The existing minus-one endpoint allowance is retained and paid explicitly. -/
theorem cube_density_09669924 (hB:ButheTheta1617) (hS:SchoenfeldTheta61)
    (hRH:RiemannHypothesis) {n:ℝ} (hn:exp 8≤n) :
    (2417481/2500000:ℝ)*n^2/log n<((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  have hg:=cube_geometry hn
  have hn0:0<n:=by linarith [hg.1]
  have hL0:0<log n:=by linarith [hg.2.1]
  have hpos:0<n^2/log n:=by positivity
  by_cases hfinite:n≤2154433
  · have hc:=finite_098 hB hn hfinite
    have hm:=mul_lt_mul_of_pos_right (by norm_num : (2417481/2500000:ℝ)<49/50) hpos
    have hid:(2417481/2500000:ℝ)*(n^2/log n)=(2417481/2500000:ℝ)*n^2/log n:=by ring
    have hid2:(49/50:ℝ)*(n^2/log n)=(49/50:ℝ)*n^2/log n:=by ring
    rw [hid,hid2] at hm
    exact hm.trans hc
  have hM:(2154433:ℝ)≤n:=le_of_not_ge hfinite
  have hmain:=main_gain hn
  have hall:=endpoint_allowance hM
  simp only [mul_div_assoc] at hmain hall ⊢
  by_cases hlate:(2160000:ℝ)≤n
  · have hc:=count_budget hS hRH (M:=2160000) (K:=33/1000) (by norm_num) hn hlate (late_budget hlate hg.2.1)
    have hmain0:n^2/log n≤((n+1)^3-n^3)/log ((n+1)^3):=by
      have hplus:0≤7/(8*(n+1))*(n^2/log n):=by positivity
      nlinarith only [hmain,hplus]
    simp only [mul_div_assoc] at hc
    nlinarith only [hc,hmain0,hall,hpos]
  · have hhi:n≤2160000:=le_of_not_ge hlate
    have hc:=count_budget hS hRH (M:=2154433) (K:=33007996/1000000000)
      (by norm_num) hn hM (seam_budget hM hg.2.1)
    simp only [mul_div_assoc] at hc
    have hgain:(7/(8*2160001):ℝ)≤7/(8*(n+1)):=by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<8*2160001) (by positivity : 0<8*(n+1))).mpr
      nlinarith
    have hcoef:((2417481/2500000:ℝ)+1/1000000000)≤1+7/(8*(n+1))-(33007996/1000000000:ℝ):=by linarith
    have hm:=mul_le_mul_of_nonneg_right hcoef hpos.le
    nlinarith only [hc,hmain,hall,hm]
end RH080.Pareto966
#print axioms RH080.Pareto966.finite_098
#print axioms RH080.Pareto966.endpoint_allowance
#print axioms RH080.Pareto966.cube_density_09669924
