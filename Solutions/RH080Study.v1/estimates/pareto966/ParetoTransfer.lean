/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ParetoScalar
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.Pareto966
open Real Finset RH080.Estimates

lemma log_step {n:ℝ} (hn:0<n) : log (n+1)≤log n+1/n := by
  have h:=log_le_sub_one_of_pos (show 0<(n+1)/n by positivity)
  rw [log_div (by positivity : n+1≠0) hn.ne'] at h
  have hid:(n+1)/n-1=1/n:=by field_simp;ring
  rw [hid] at h
  linarith

lemma main_gain {n:ℝ} (hn:exp 8≤n) :
    (1+7/(8*(n+1)))*n^2/log n≤((n+1)^3-n^3)/log ((n+1)^3) := by
  have hg:=cube_geometry hn
  have hn0:0<n:=by linarith [hg.1]
  have hL:8≤log n:=hg.2.1
  have hL0:0<log n:=by linarith
  have hb0:=hg.2.2.2.2
  have hb:log ((n+1)^3)=3*log (n+1):=by rw [log_pow];norm_num
  have hs:=mul_le_mul_of_nonneg_left (log_step hn0) hn0.le
  have hi:n*(log n+1/n)=n*log n+1:=by field_simp
  rw [hi] at hs
  have hp:=mul_le_mul_of_nonneg_left hs (show 0≤3*(8*n+15)*n by positivity)
  have h1:=mul_nonneg (sq_nonneg n) (show 0≤log n-8 by linarith)
  have h2:=mul_nonneg hn0.le (show 0≤32*log n-45 by linarith)
  have hw:(8*n+15)*n^2*log ((n+1)^3)≤8*(n+1)*((n+1)^3-n^3)*log n:=by
    rw [hb]
    nlinarith only [hp,h1,h2,hL]
  apply (div_le_div_iff₀ hL0 hb0).mpr
  apply (mul_le_mul_iff_of_pos_right (show 0<8*(n+1) by positivity)).mp
  have hid:((1+7/(8*(n+1)))*n^2*log ((n+1)^3))*(8*(n+1))=
      (8*n+15)*n^2*log ((n+1)^3):=by field_simp;ring
  rw [hid]
  nlinarith only [hw]

lemma tight_geometry {M n:ℝ} (hM:(2000:ℝ)≤M) (hn:M≤n) :
    sqrt ((n+1)^3)≤(1+2/M)*n*sqrt n ∧
    log ((n+1)^3)≤3*log n+3/M := by
  have hM0:0<M:=by linarith
  have hn0:0<n:=hM0.trans_le hn
  have hsr:sqrt ((n+1)^3)≤(n+2)*sqrt n:=by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hid:((n+2)*sqrt n)^2=(n+2)^2*n:=by rw [mul_pow,sq_sqrt hn0.le]
    rw [hid]
    nlinarith [sq_nonneg n]
  have hratio:2≤(2/M)*n:=by rw [div_mul_eq_mul_div];exact (le_div_iff₀ hM0).mpr (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2))
  have hs:sqrt ((n+1)^3)≤(1+2/M)*n*sqrt n:=hsr.trans
    (mul_le_mul_of_nonneg_right (show n+2≤(1+2/M)*n by nlinarith) (sqrt_nonneg n))
  have hq:1/n≤1/M:=one_div_le_one_div_of_le hM0 hn
  have hl:=log_step hn0
  refine ⟨hs,?_⟩
  rw [log_pow];norm_num
  simp only [div_eq_mul_inv,one_mul] at hq hl ⊢
  linarith

/-- Exact source errors divided by the endpoint logarithm, using a global
quadratic/exponential budget and the original full theta source. -/
lemma source_error_budget {M K n:ℝ} (hM:(2000:ℝ)≤M) (hn8:exp 8≤n) (hn:M≤n)
    (hbudget:(1+1/M)*(3*log n+3/M-2)*log n<K*(4*π)*sqrt n) :
    sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π) <
      K*n^2/log n*log ((n+1)^3) := by
  have hg:=cube_geometry hn8
  have hn0:0<n:=by linarith [hg.1]
  have hM0:0<M:=by linarith
  have hq:0<1/M:=by positivity
  have hL:8≤log n:=hg.2.1
  have hL0:0<log n:=by linarith
  have hb0:=hg.2.2.2.2
  have ht:=tight_geometry hM hn
  have hlogmon:3*log n≤log ((n+1)^3):=by
    rw [log_pow];norm_num;linarith [log_le_log hn0 (show n≤n+1 by linarith)]
  have ha:log (n^3)=3*log n:=by rw [log_pow];norm_num
  have hs:sqrt (n^3)=n*sqrt n:=by
    rw [show n^3=n^2*n by ring,sqrt_mul (sq_nonneg n),sqrt_sq hn0.le]
  have hA:(3*log n-2)*(3*log n)≤(3*log n+3/M-2)*log ((n+1)^3):=by
    apply mul_le_mul (by linarith) hlogmon (by linarith) (by linarith)
  have hA2:=mul_le_mul_of_nonneg_left hA (show 0≤n*sqrt n by positivity)
  have hB:(log ((n+1)^3)-2)*log ((n+1)^3)≤
      (3*log n+3/M-2)*log ((n+1)^3):=mul_le_mul_of_nonneg_right (by linarith [ht.2]) hb0.le
  have hB2:=mul_le_mul ht.1 hB (by nlinarith) (by positivity : 0≤(1+2/M)*n*sqrt n)
  have hnum:n*sqrt n*(3*log n-2)*(3*log n)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)≤
      (2+2/M)*n*sqrt n*(3*log n+3/M-2)*log ((n+1)^3):=by nlinarith only [hA2,hB2]
  have hpi:0<8*π:=by positivity
  have htotal:sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π)≤
      ((1+1/M)*n*sqrt n*(3*log n+3/M-2)/(4*π))*log ((n+1)^3):=by
    rw [←add_div,hs,ha]
    apply (div_le_iff₀ hpi).mpr
    have hid:((1+1/M)*n*sqrt n*(3*log n+3/M-2)/(4*π))*log ((n+1)^3)*(8*π)=
        (2+2/M)*n*sqrt n*(3*log n+3/M-2)*log ((n+1)^3):=by field_simp;ring
    rw [hid]
    exact hnum
  have hscaled:((1+1/M)*n*sqrt n*(3*log n+3/M-2))*log n<K*n^2*(4*π):=by
    calc
      _=((1+1/M)*(3*log n+3/M-2)*log n)*(n*sqrt n):=by ring
      _<(K*(4*π)*sqrt n)*(n*sqrt n):=mul_lt_mul_of_pos_right hbudget (by positivity)
      _=K*(4*π)*n*(sqrt n)^2:=by ring
      _=_:=by rw [sq_sqrt hn0.le];ring
  have hcap:(1+1/M)*n*sqrt n*(3*log n+3/M-2)/(4*π)<K*n^2/log n:=by
    exact (div_lt_div_iff₀ (by positivity : 0<4*π) hL0).mpr hscaled
  exact htotal.trans_lt (mul_lt_mul_of_pos_right hcap hb0)

lemma count_budget (hS:SchoenfeldTheta61) (hRH:RiemannHypothesis)
    {M K n:ℝ} (hM:(2000:ℝ)≤M) (hn8:exp 8≤n) (hn:M≤n)
    (hbudget:(1+1/M)*(3*log n+3/M-2)*log n<K*(4*π)*sqrt n) :
    ((n+1)^3-n^3)/log ((n+1)^3)-K*n^2/log n-1<
      ((openPrimes (n^3) ((n+1)^3)).card:ℝ) := by
  have hb0:0<log ((n+1)^3):=(cube_geometry hn8).2.2.2.2
  have he:=source_error_budget hM hn8 hn hbudget
  have hcount:=cube_count_schoenfeld_explicit hS hRH hn8
  have hediv:(sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π))/log ((n+1)^3)<K*n^2/log n := (div_lt_iff₀ hb0).mpr he
  have hid:(((n+1)^3-n^3-sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)-
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π))/log ((n+1)^3)-1)=
      ((n+1)^3-n^3)/log ((n+1)^3)-
      (sqrt (n^3)*(log (n^3)-2)*log (n^3)/(8*π)+
      sqrt ((n+1)^3)*(log ((n+1)^3)-2)*log ((n+1)^3)/(8*π))/log ((n+1)^3)-1:=by ring
  rw [hid] at hcount
  linarith

end RH080.Pareto966
#print axioms RH080.Pareto966.main_gain
#print axioms RH080.Pareto966.count_budget
