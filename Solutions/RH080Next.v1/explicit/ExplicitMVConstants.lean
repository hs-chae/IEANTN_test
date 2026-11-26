/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitPrimeWeights
import ExplicitWindowErrors

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.Explicit

def mvBlockLength (c t k : ℝ) : ℝ := exp ((t+halfLogWidth c t)/2)/k

def mvBlockDenom (k t : ℝ) : ℝ := 1-2*log k/t

def mvNumerator (c t R : ℝ) : ℝ :=
  4*((t+(1+R)*halfLogWidth c t)/t)*exp (3*R*halfLogWidth c t/2)

/-- Both original block choices k=1 and k=16, with their exact logarithmic
denominators. No fixed-k or asymptotic denominator is substituted. -/
theorem mv_block_parameters (c t k : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) (hk : 1 ≤ k) (hk16 : k ≤ 16) :
    1 < mvBlockLength c t k ∧
    log (mvBlockLength c t k) = (t+halfLogWidth c t)/2-log k ∧
    0 < mvBlockDenom k t ∧ 0 < mvBlockDenom k 42 ∧
    mvBlockDenom k 42 ≤ mvBlockDenom k t := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hk0 : 0 < k := by linarith
  have hl0 : 0 ≤ log k := log_nonneg hk
  have hlu : log k ≤ 15 := by
    have h := log_le_sub_one_of_pos hk0
    linarith
  have heq : mvBlockLength c t k = exp ((t+halfLogWidth c t)/2-log k) := by
    unfold mvBlockLength
    rw [exp_sub,exp_log hk0]
  have hlog : log (mvBlockLength c t k) = (t+halfLogWidth c t)/2-log k := by rw [heq,log_exp]
  have hq : 0 < mvBlockDenom k t := by
    unfold mvBlockDenom
    have h : 2*log k/t < 1 := (div_lt_one (by linarith : 0 < t)).mpr (by linarith)
    linarith
  have hq42 : 0 < mvBlockDenom k 42 := by unfold mvBlockDenom; linarith
  have hmono : mvBlockDenom k 42 ≤ mvBlockDenom k t := by
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*log k) (by norm_num : (0:ℝ)<42) ht
    unfold mvBlockDenom
    linarith
  refine ⟨?_,hlog,hq,hq42,hmono⟩
  rw [heq]
  exact one_lt_exp_iff.mpr (by linarith)

/-- The actual extra radius/center exponential factors fit strictly inside
the unchanged numerical coefficient B=4.00001 throughout the continuum. -/
theorem mv_numerator_lt (c t R : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) (hR0 : 0 ≤ R) (hR : R ≤ 10) :
    mvNumerator c t R < (400001/100000:ℝ) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hd0 := hd.1.le
  have ht0 : 0 < t := by linarith
  have hratio : (t+(1+R)*halfLogWidth c t)/t ≤ (10000001/10000000:ℝ) := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith
  have hq0 : 0 ≤ 3*R*halfLogWidth c t/2 := by positivity
  have hqu : 3*R*halfLogWidth c t/2 ≤ (3/10000000:ℝ) := by nlinarith
  have he := exp_bound_div_one_sub_of_interval hq0 (by linarith : 3*R*halfLogWidth c t/2 < 1)
  have hecap : exp (3*R*halfLogWidth c t/2) ≤ (1000001/1000000:ℝ) := by
    apply he.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-3*R*halfLogWidth c t/2)).mpr
    nlinarith
  have hp := mul_le_mul hratio hecap (exp_pos _).le (by norm_num : (0:ℝ)≤10000001/10000000)
  unfold mvNumerator
  nlinarith

/-- The two exact wing coefficients supplied by actual MV+BV estimates are
bounded by the original B/q(t) times mass and entrance terms. -/
theorem mv_wing_coefficients (c t R k : ℝ)
    (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hR0 : 0 ≤ R) (hR : R ≤ 10) (hk : 1 ≤ k) (hk16 : k ≤ 16) :
    2*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*
        halfLogWidth c t*exp ((t+halfLogWidth c t)+R*halfLogWidth c t)/
        log (mvBlockLength c t k) ≤
      ((400001/100000:ℝ)/mvBlockDenom k t)*poleScale c t ∧
    4*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*
        mvBlockLength c t k/log (mvBlockLength c t k) ≤
      ((400001/100000:ℝ)/mvBlockDenom k t)*(2/k) := by
  let d := halfLogWidth c t
  let L := t+d
  let lam := R*d
  let ell := mvBlockLength c t k
  let q := mvBlockDenom k t
  let N := mvNumerator c t R
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hd0 : 0 ≤ d := hd.le
  have hlam : 0 ≤ lam := mul_nonneg hR0 hd0
  have ht0 : 0 < t := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨hell,hlog,hq,hq42,hqmono⟩ := mv_block_parameters c t k hc hc1 ht hk hk16
  have hz : 0 < t/2-log k := by
    have heq : t/2-log k = t*q/2 := by dsimp [q,mvBlockDenom]; field_simp <;> ring
    rw [heq]
    positivity
  have hloglower : t/2-log k ≤ log ell := by dsimp [ell]; rw [hlog]; linarith
  have hN : N ≤ (400001/100000:ℝ) := (mv_numerator_lt c t R hc hc1 ht hR0 hR).le
  have hN0 : 0 ≤ N := by dsimp [N,mvNumerator]; positivity
  have hQ0 : 0 ≤ exteriorPrimeWeight d L R := by dsimp [exteriorPrimeWeight,L]; positivity
  have hnum1 : 0 ≤ 2*exteriorPrimeWeight d L R*d*exp (L+lam) := by positivity
  have hnum2 : 0 ≤ 4*exteriorPrimeWeight d L R*ell := by
    have hell0 : 0 < ell := lt_trans zero_lt_one hell
    positivity
  have hlead := div_le_div_of_nonneg_left hnum1 hz hloglower
  have hend := div_le_div_of_nonneg_left hnum2 hz hloglower
  have hleadEq : 2*exteriorPrimeWeight d L R*d*exp (L+lam)/(t/2-log k) = (N/q)*poleScale c t := by
    have he : exp (L+lam)/exp ((L-lam)/2) = exp (L/2)*exp (3*lam/2) := by
      rw [←exp_sub,←exp_add]
      congr 1
      ring
    dsimp [exteriorPrimeWeight]
    rw [show 2*((L+R*d)/exp ((L-R*d)/2))*d*exp (L+lam)/(t/2-log k) =
      (2*(L+lam)*d/(t/2-log k))*(exp (L+lam)/exp ((L-lam)/2)) by dsimp [lam]; ring,he]
    dsimp [N,mvNumerator,q,mvBlockDenom,poleScale,L,lam,d]
    rw [show (t+halfLogWidth c t)/2 = t/2+halfLogWidth c t/2 by ring]
    field_simp
    <;> ring
  have hendEq : 4*exteriorPrimeWeight d L R*ell/(t/2-log k) =
      (4*(L+lam)/(k*(t/2-log k)))*exp (lam/2) := by
    have he : exp (L/2)/exp ((L-lam)/2) = exp (lam/2) := by rw [←exp_sub]; congr 1; ring
    dsimp [exteriorPrimeWeight,ell,mvBlockLength]
    change 4*((L+lam)/exp ((L-lam)/2))*(exp (L/2)/k)/(t/2-log k) = _
    rw [show 4*((L+lam)/exp ((L-lam)/2))*(exp (L/2)/k)/(t/2-log k) =
      (4*(L+lam)/(k*(t/2-log k)))*(exp (L/2)/exp ((L-lam)/2)) by field_simp <;> ring,he]
  have hendBound : 4*exteriorPrimeWeight d L R*ell/(t/2-log k) ≤ (N/q)*(2/k) := by
    rw [hendEq]
    have he := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith : lam/2 ≤ 3*lam/2))
      (by dsimp [L]; positivity : 0 ≤ 4*(L+lam)/(k*(t/2-log k)))
    apply he.trans_eq
    dsimp [N,mvNumerator,q,mvBlockDenom,L,lam,d]
    field_simp
    <;> ring
  have hratio : N/q ≤ (400001/100000:ℝ)/q := div_le_div_of_nonneg_right hN hq.le
  refine ⟨?_,?_⟩
  · change 2*exteriorPrimeWeight d L R*d*exp (L+lam)/log ell ≤ _
    rw [hleadEq] at hlead
    exact hlead.trans (mul_le_mul_of_nonneg_right hratio (by unfold poleScale; positivity))
  · change 4*exteriorPrimeWeight d L R*ell/log ell ≤ _
    exact hend.trans (hendBound.trans (mul_le_mul_of_nonneg_right hratio (by positivity)))

/-- Removing the finite-width MV denominator costs exactly the recorded
k-dependent constant. Its t-dependence is bounded analytically throughout
the ray, with the literal k=1 or k=16 retained. -/
theorem mv_wing_allowance_linearized (c t R k J H : ℝ)
    (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hR0 : 0 ≤ R) (hR : R ≤ 10) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hJ : 0 ≤ J) (hH : 0 ≤ H) :
    (2*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*
        halfLogWidth c t*exp ((t+halfLogWidth c t)+R*halfLogWidth c t)/
        log (mvBlockLength c t k))*J+
    (4*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*
        mvBlockLength c t k/log (mvBlockLength c t k))*H ≤
      (400001/100000:ℝ)*poleScale c t*J+
      (400001/100000:ℝ)*J*c*log k/mvBlockDenom k 42+
      2*(400001/100000:ℝ)*H/(k*mvBlockDenom k 42) := by
  let B : ℝ := 400001/100000
  let q := mvBlockDenom k t
  let q0 := mvBlockDenom k 42
  have ht0 : 0 < t := by linarith
  have hk0 : 0 < k := by linarith
  have hlog : 0 ≤ log k := log_nonneg hk
  obtain ⟨hell,helog,hq,hq0,hqmono⟩ := mv_block_parameters c t k hc hc1 ht hk hk16
  obtain ⟨hLead,hEnd⟩ := mv_wing_coefficients c t R k hc hc1 ht hR0 hR hk hk16
  have hc0 : 0 ≤ c := by linarith
  have hq1 : q ≤ 1 := by
    have hh : 0 ≤ 2*log k/t := by positivity
    dsimp [q,mvBlockDenom]
    linarith
  have hdiff : 0 ≤ B/q-B := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hq).mpr
    dsimp [B]
    nlinarith
  have hqt : q*t = t-2*log k := by dsimp [q,mvBlockDenom]; field_simp
  have hdiffeq : B/q-B = 2*B*log k/(t*q) := by
    apply (eq_div_iff (mul_ne_zero ht0.ne' (show q ≠ 0 from hq.ne'))).mpr
    calc
      (B/q-B)*(t*q) = B*t-B*(q*t) := by field_simp [show q ≠ 0 from hq.ne'] <;> ring
      _ = 2*B*log k := by rw [hqt]; ring
  have hp := poleScale_upper c t hc hc1 ht
  have hp0 : 0 ≤ poleScale c t := by
    have hd := (halfLogWidth_bounds c t hc hc1 ht).1
    unfold poleScale
    positivity
  have hExtra : (B/q-B)*poleScale c t*J ≤ B*J*c*log k/q0 := by
    have h0 := mul_le_mul_of_nonneg_left hp hdiff
    have h1 := mul_le_mul_of_nonneg_right h0 hJ
    have heq : (B/q-B)*(c*t/2)*J = B*J*c*log k/q := by rw [hdiffeq]; field_simp <;> ring
    rw [heq] at h1
    have h2 : B*J*c*log k/q ≤ B*J*c*log k/q0 := by
      exact div_le_div_of_nonneg_left (by dsimp [B]; positivity) hq0 hqmono
    exact h1.trans h2
  have hEnd0 : (B/q)*(2/k)*H ≤ 2*B*H/(k*q0) := by
    have hratio : 1/q ≤ 1/q0 := one_div_le_one_div_of_le hq0 hqmono
    have hh := mul_le_mul_of_nonneg_left hratio (by dsimp [B]; positivity : 0 ≤ 2*B*H/k)
    calc
      _ = (2*B*H/k)*(1/q) := by ring
      _ ≤ (2*B*H/k)*(1/q0) := hh
      _ = _ := by field_simp <;> ring
  have hL := mul_le_mul_of_nonneg_right hLead hJ
  have hE := mul_le_mul_of_nonneg_right hEnd hH
  change _ ≤ (B/q)*poleScale c t*J at hL
  change _ ≤ (B/q)*(2/k)*H at hE
  have hCombine : (B/q)*poleScale c t*J ≤ B*poleScale c t*J+B*J*c*log k/q0 := by
    nlinarith
  change _ ≤ B*poleScale c t*J+B*J*c*log k/q0+2*B*H/(k*q0)
  linarith

#print axioms mv_wing_allowance_linearized
#print axioms mv_block_parameters
#print axioms mv_numerator_lt
#print axioms mv_wing_coefficients
end RH080Next.Explicit
