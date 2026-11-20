/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import Mathlib
import RamanujanPV.QuantitativeTail

/-!
# Source-audited Ramanujan analytic transition

This file proves mathematical and arithmetic implications only. Source-first C
verification is separate. Analytic source identities, where not rederived from
IEANTN's principal-value definition, remain explicit theorem hypotheses.
-/
namespace RamanujanPV.AnalyticTransition
open Real Set Finset Filter MeasureTheory
set_option maxHeartbeats 0

/-- Every nonnegative sequence with ratio bounded by `r` has the stated tail.
This is the generic theorem used for the positive Ei Taylor series. -/
theorem geometric_tail {f : ℕ → ℝ} {r : ℝ} (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ k, f (N + k + 1) ≤ r * f (N + k)) :
    Summable (fun k => f (N + k)) ∧
      (∑' k, f (N + k)) ≤ f N / (1-r) := by
  have hbound : ∀ k, f (N+k) ≤ f N * r^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        f (N+(k+1)) ≤ r*f (N+k) := by simpa [Nat.add_assoc] using hstep k
        _ ≤ r*(f N*r^k) := mul_le_mul_of_nonneg_left ih hr0
        _ = f N*r^(k+1) := by ring
  have hg : Summable (fun k : ℕ => f N*r^k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (f N)
  have hs : Summable (fun k => f (N+k)) :=
    Summable.of_nonneg_of_le (fun k => hf _) hbound hg
  refine ⟨hs, ?_⟩
  calc
    (∑' k, f (N+k)) ≤ ∑' k : ℕ, f N*r^k := hs.tsum_le_tsum hbound hg
    _ = f N / (1-r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      rfl

/-- Taylor term number `n+1` in DLMF 6.6.1. -/
noncomputable def eiTerm (z : ℝ) (n : ℕ) : ℝ :=
  z^(n+1)/((n+1:ℝ)*(Nat.factorial (n+1):ℝ))

lemma eiTerm_nonneg {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : 0 ≤ eiTerm z n := by
  unfold eiTerm
  positivity

lemma eiTerm_succ (z : ℝ) (n : ℕ) :
    eiTerm z (n+1) = eiTerm z n*z*(n+1)/(n+2)^2 := by
  unfold eiTerm
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (n+1:ℝ) ≠ 0 := by positivity
  have h2 : (n+2:ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (n+1):ℝ) ≠ 0 := by positivity
  rw [show n+1+1=n+2 by omega, pow_succ]
  field_simp
  <;> ring

lemma summable_eiTerm {z : ℝ} (hz : 0 ≤ z) : Summable (eiTerm z) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial z)
  apply Summable.of_nonneg_of_le (fun n => eiTerm_nonneg hz n) _ h
  intro n
  change z^(n+1)/((n+1:ℝ)*(Nat.factorial (n+1):ℝ)) ≤
    z^(n+1)/(Nat.factorial (n+1):ℝ)
  apply div_le_div_of_nonneg_left (pow_nonneg hz _) (by positivity)
  have hp : 0 ≤ (Nat.factorial (n+1):ℝ) := by positivity
  nlinarith

/-- For `0≤z≤45`, all terms after the first 200 contract by at most one quarter. -/
lemma eiTerm_ratio {z : ℝ} (hz : 0 ≤ z) (hz45 : z ≤ 45) {n : ℕ}
    (hn : 200 ≤ n) : eiTerm z (n+1) ≤ (1/4:ℝ)*eiTerm z n := by
  rw [eiTerm_succ]
  have ht := eiTerm_nonneg hz n
  have hn' : (200:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < (n+2)^2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hq : z*(n+1) ≤ (1/4:ℝ)*(n+2)^2 := by
    have hs : 0 ≤ (n-200:ℝ)^2 := sq_nonneg _
    nlinarith
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hq)]

/-- Sound analytic remainder enclosure for the actual infinite Ei series.
Its assumptions concern `z`, not the positivity of the Ramanujan endpoint. -/
theorem ei_series_remainder {z : ℝ} (hz : 0 ≤ z) (hz45 : z ≤ 45) :
    0 ≤ (∑' n, eiTerm z n) - ∑ n ∈ range 200, eiTerm z n ∧
    (∑' n, eiTerm z n) - ∑ n ∈ range 200, eiTerm z n ≤
      (4/3:ℝ)*eiTerm z 200 := by
  have hs := summable_eiTerm hz
  have he := hs.sum_add_tsum_nat_add 200
  have ht := geometric_tail 200 (eiTerm_nonneg hz) (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1) (fun k => eiTerm_ratio hz hz45 (by omega : 200 ≤ 200+k))
  have he' : (∑' n, eiTerm z n) - ∑ n ∈ range 200, eiTerm z n =
      ∑' k, eiTerm z (200+k) := by
    have he2 : (∑ n ∈ range 200, eiTerm z n) + (∑' k, eiTerm z (200+k)) =
        ∑' n, eiTerm z n := by simpa only [Nat.add_comm] using he
    linarith
  rw [he']
  constructor
  · exact tsum_nonneg (fun k => eiTerm_nonneg hz _)
  · convert ht.2 using 1 <;> ring

/-- Mathlib supplies a substantially sharper bound; the endpoint evaluator
only needs this deliberately coarse enclosure. -/
theorem euler_gamma_unit :
    0 ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ 1 := by
  constructor
  · linarith [Real.one_half_lt_eulerMascheroniConstant]
  · linarith [Real.eulerMascheroniConstant_lt_two_thirds]

#print axioms geometric_tail
#print axioms ei_series_remainder
#print axioms euler_gamma_unit

/- Generic analytic log proof recompiled from ScopedWinnerSourcePV.v1/src/SynergyAnalytic/LogAtanh.lean.
No inherited application proof object is imported. -/
noncomputable def logAtanhPoly (n : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, 2*r^(2*k+1)/(2*k+1:ℕ)
noncomputable def logAtanhError (n : ℕ) (r : ℝ) : ℝ :=
  Real.log (1+r)-Real.log (1-r)-logAtanhPoly n r

theorem logAtanhPoly_deriv (n : ℕ) (r : ℝ) :
    HasDerivAt (logAtanhPoly n) (2*∑ k ∈ Finset.range n, r^(2*k)) r := by
  have hd : ∀ k ∈ Finset.range n,
      HasDerivAt (fun r : ℝ => 2*r^(2*k+1)/(2*k+1:ℕ)) (2*r^(2*k)) r := by
    intro k hk
    have hk0 : (2*k+1:ℝ) ≠ 0 := by positivity
    convert (((hasDerivAt_id r).pow (2*k+1)).const_mul 2).div_const (2*k+1:ℕ) using 1 <;>
      first | rfl | (norm_num <;> field_simp <;> ring)
  convert HasDerivAt.fun_sum hd using 1 <;> first | rfl | simp only [logAtanhPoly, Finset.mul_sum]

theorem logAtanh_geom (n : ℕ) (r : ℝ) :
    (1-r^2)*(∑ k ∈ Finset.range n, r^(2*k)) = 1-r^(2*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : r^(2*(n+1)) = r^(2*n)*r^2 := by rw [Nat.mul_add,pow_add] <;> norm_num
    rw [he]
    nlinarith

theorem logAtanhError_deriv {r : ℝ} (hr : -(1:ℝ) < r) (hr1 : r < 1) (n : ℕ) :
    HasDerivAt (logAtanhError n) (2*r^(2*n)/(1-r^2)) r := by
  have hp : (1:ℝ)+r ≠ 0 := by linarith
  have hm : (1:ℝ)-r ≠ 0 := by linarith
  have hq : (1:ℝ)-r^2 ≠ 0 := by nlinarith
  have h1 := ((hasDerivAt_id r).const_add 1).log hp
  have h2 := ((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log hm
  have hd := (h1.sub h2).sub (logAtanhPoly_deriv n r)
  have hg := logAtanh_geom n r
  convert hd using 1 <;> first | rfl | (dsimp; field_simp [hp,hm,hq]; nlinarith)


/- Generic analytic log proof recompiled from ScopedWinnerSourcePV.v1/src/SynergyAnalytic/LogBounds.lean.
No inherited application proof object is imported. -/
/-- A uniform analytic bound for the exact 80-term source series. The source
adds one128-bit quantum to the upper endpoint; arithmetic rounding remains
in the separately verified directed operations. -/
theorem log_atanh80_error {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1/2) :
    0 ≤ logAtanhError 80 r ∧ logAtanhError 80 r ≤ 1/(2:ℝ)^128 := by
  let f : ℝ → ℝ := fun x => 2*x^160/(1-x^2)
  have hden : ∀ x ∈ Icc (0:ℝ) r, 0 < 1-x^2 := by
    intro x hx
    nlinarith [hx.1,hx.2]
  have hc : ContinuousOn f (Icc 0 r) := by
    unfold f
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact (hden x hx).ne'
  have hi : IntervalIntegrable f volume 0 r := hc.intervalIntegrable_of_Icc hr
  have hd : ∀ x ∈ uIcc (0:ℝ) r, HasDerivAt (logAtanhError 80) (f x) x := by
    intro x hx
    rw [uIcc_of_le hr] at hx
    simpa [f] using logAtanhError_deriv (by linarith [hx.1]) (by linarith [hx.2]) 80
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hz : logAtanhError 80 0 = 0 := by simp [logAtanhError,logAtanhPoly]
  rw [hz,sub_zero] at he
  have hf0 : ∀ x ∈ Icc (0:ℝ) r, 0 ≤ f x := by
    intro x hx
    exact div_nonneg (by positivity) (hden x hx).le
  have hfu : ∀ x ∈ Icc (0:ℝ) r, f x ≤ 1/(2:ℝ)^128 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx2 : x ≤ (1/2:ℝ) := hx.2.trans hr2
    have hp : x^160 ≤ (1/2:ℝ)^160 := pow_le_pow_left₀ hx0 hx2 160
    have hq : (3/4:ℝ) ≤ 1-x^2 := by nlinarith
    have hb : f x ≤ 2*(1/2:ℝ)^160/(3/4:ℝ) := by
      unfold f
      exact div_le_div₀ (by positivity) (by nlinarith) (by norm_num) hq
    exact hb.trans (by norm_num)
  have hlo := intervalIntegral.integral_nonneg (μ:=volume) hr hf0
  have hup := intervalIntegral.integral_mono_on hr hi (intervalIntegrable_const)
    hfu
  rw [he] at hlo hup
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hup
  refine ⟨hlo,?_⟩
  have hq : 0 < 1/(2:ℝ)^128 := by positivity
  nlinarith

theorem log_atanh80_bounds {r lo hi : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1/2)
    (hl : lo ≤ logAtanhPoly 80 r) (hu : logAtanhPoly 80 r ≤ hi) :
    lo ≤ Real.log ((1+r)/(1-r)) ∧
      Real.log ((1+r)/(1-r)) ≤ hi+1/(2:ℝ)^128 := by
  have he := log_atanh80_error hr hr2
  have hp : (1:ℝ)+r ≠ 0 := by linarith
  have hm : (1:ℝ)-r ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  unfold logAtanhError at he
  constructor <;> linarith


lemma eiTerm_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    eiTerm a n ≤ eiTerm b n := by
  unfold eiTerm
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab _) (by positivity)

noncomputable def eiPartial (z : ℝ) : ℝ := ∑ n ∈ range 200, eiTerm z n

/-- A generic exact enclosure statement; its finite arithmetic premises can be
proved by kernel reduction of rational Taylor sums. -/
theorem ei_series_bounds {z a b lo hi : ℝ} (ha : 0 ≤ a) (haz : a ≤ z)
    (hzb : z ≤ b) (hb : b ≤ 45)
    (hl : lo ≤ eiPartial a) (hu : eiPartial b+(4/3:ℝ)*eiTerm b 200 ≤ hi) :
    lo ≤ ∑' n, eiTerm z n ∧ (∑' n, eiTerm z n) ≤ hi := by
  have hz := ha.trans haz
  have hr := ei_series_remainder hz (hzb.trans hb)
  have hpl : eiPartial a ≤ eiPartial z :=
    Finset.sum_le_sum (fun n _ => eiTerm_mono ha haz n)
  have hpu : eiPartial z ≤ eiPartial b :=
    Finset.sum_le_sum (fun n _ => eiTerm_mono hz hzb n)
  have ht : eiTerm z 200 ≤ eiTerm b 200 := eiTerm_mono hz hzb 200
  change 0 ≤ (∑' n, eiTerm z n)-eiPartial z ∧
    (∑' n, eiTerm z n)-eiPartial z ≤ (4/3:ℝ)*eiTerm z 200 at hr
  constructor <;> linarith

/-- The exact source identity DLMF 6.2.8 and 6.6.1. Its link to the
principal-value IEANTN definition is explicitly external until separately proved. -/
def LogIntegralSeriesIdentity (li : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 1 < x → li x = Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' n, eiTerm (Real.log x) n

/-- DLMF's identity plus checked Taylor enclosures gives an actual li bound.
No endpoint positivity is assumed. -/
theorem li_from_series {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    {x a b llo lhi slo shi : ℝ} (hx : 1 < x) (ha : 0 ≤ a)
    (haz : a ≤ Real.log x) (hzb : Real.log x ≤ b) (hb : b ≤ 45)
    (hll : llo ≤ Real.log (Real.log x)) (hlu : Real.log (Real.log x) ≤ lhi)
    (hsl : slo ≤ eiPartial a) (hsu : eiPartial b+(4/3:ℝ)*eiTerm b 200 ≤ shi) :
    llo+slo ≤ li x ∧ li x ≤ 1+lhi+shi := by
  rw [hseries x hx]
  have ht := ei_series_bounds ha haz hzb hb hsl hsu
  have hg := euler_gamma_unit
  constructor <;> linarith

#print axioms log_atanh80_bounds
#print axioms ei_series_bounds
#print axioms li_from_series

set_option maxRecDepth 10000
lemma endpoint_series_n_lower :
    (55206531495:ℝ) ≤ eiPartial (280297972358859/10000000000000:ℝ) := by
  norm_num [eiPartial, eiTerm, Finset.sum_range_succ, Nat.factorial]

#print axioms endpoint_series_n_lower

lemma endpoint_series_n_upper :
    eiPartial (280297972358860/10000000000000:ℝ) +
      (4/3:ℝ)*eiTerm (280297972358860/10000000000000:ℝ) 200 ≤ 55206531496 := by
  norm_num [eiPartial, eiTerm, Finset.sum_range_succ, Nat.factorial]

lemma endpoint_series_ne_lower :
    (21092171544:ℝ) ≤ eiPartial (270297972358859/10000000000000:ℝ) := by
  norm_num [eiPartial, eiTerm, Finset.sum_range_succ, Nat.factorial]

lemma endpoint_series_ne_upper :
    eiPartial (270297972358860/10000000000000:ℝ) +
      (4/3:ℝ)*eiTerm (270297972358860/10000000000000:ℝ) 200 ≤ 21092171545 := by
  norm_num [eiPartial, eiTerm, Finset.sum_range_succ, Nat.factorial]

lemma log_two_decimal :
    (6931471805599453/10000000000000000:ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599454/10000000000000000 := by
  have h := log_atanh80_bounds (r:=(1/3:ℝ))
    (lo:=(6931471805599453/10000000000000000:ℝ))
    (hi:=(69314718055994531/100000000000000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
  norm_num at h
  constructor
  · exact h.1
  · exact h.2.trans (by norm_num)

lemma log_endpoint_mantissa :
    (3039100134881036/10000000000000000:ℝ) ≤
        Real.log ((1+(381336301/2528819949:ℝ))/(1-(381336301/2528819949:ℝ))) ∧
      Real.log ((1+(381336301/2528819949:ℝ))/(1-(381336301/2528819949:ℝ))) ≤
        3039100134881037/10000000000000000 := by
  have h := log_atanh80_bounds (r:=(381336301/2528819949:ℝ))
    (lo:=(3039100134881036/10000000000000000:ℝ))
    (hi:=(30391001348810361/100000000000000000:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
    (by norm_num [logAtanhPoly,Finset.sum_range_succ])
  exact ⟨h.1,h.2.trans (by norm_num)⟩

lemma log_endpoint_bounds :
    (280297972358859/10000000000000:ℝ) ≤ Real.log 1490000000000 ∧
      Real.log 1490000000000 ≤ 280297972358860/10000000000000 := by
  let q : ℝ := (1+(381336301/2528819949:ℝ))/(1-(381336301/2528819949:ℝ))
  have hq : (0:ℝ) < q := by dsimp [q]; norm_num
  have hid : Real.log (1490000000000:ℝ) = 40*Real.log 2+Real.log q := by
    calc
      _ = Real.log ((2:ℝ)^40*q) := by congr 1; dsimp [q]; norm_num
      _ = Real.log ((2:ℝ)^40)+Real.log q := Real.log_mul (by positivity) hq.ne'
      _ = 40*Real.log 2+Real.log q := by rw [Real.log_pow]; norm_num
  have h2 := log_two_decimal
  have hq2 := log_endpoint_mantissa
  change _ ≤ Real.log q ∧ Real.log q ≤ _ at hq2
  rw [hid]
  constructor <;> linarith

lemma log_log_coarse {z : ℝ} (hz27 : 27 ≤ z) (hz29 : z ≤ 29) :
    3 ≤ Real.log z ∧ Real.log z ≤ 4 := by
  have hz : 0 < z := by linarith
  have he3 : Real.exp 3 < 27 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num : (3:ℕ) ≠ 0)
    calc
      Real.exp 3 = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 27 := by simpa only [show (3:ℝ)^3 = 27 by norm_num] using hp
  have he4 : 29 < Real.exp 4 := by
    have he : (5/2:ℝ) < Real.exp 1 := (by norm_num : (5/2:ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
    have hp := pow_lt_pow_left₀ he (by norm_num : (0:ℝ) ≤ 5/2) (by norm_num : (4:ℕ) ≠ 0)
    have heq : (Real.exp 1)^4 = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq] at hp
    norm_num at hp
    linarith
  exact ⟨(Real.le_log_iff_exp_le hz).mpr (he3.le.trans hz27),
    (Real.log_le_iff_le_exp hz).mpr (hz29.trans he4.le)⟩

#print axioms endpoint_series_n_upper
#print axioms endpoint_series_ne_upper
#print axioms log_endpoint_bounds

lemma li_endpoint_bounds {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    (55206531498:ℝ) ≤ li 1490000000000 ∧ li 1490000000000 ≤ 55206531501 := by
  have hL := log_endpoint_bounds
  have hlog := log_log_coarse (by linarith [hL.1] : 27 ≤ Real.log 1490000000000)
    (by linarith [hL.2] : Real.log 1490000000000 ≤ 29)
  have h := li_from_series hseries (x:=1490000000000)
    (a:=(280297972358859/10000000000000:ℝ))
    (b:=(280297972358860/10000000000000:ℝ))
    (by norm_num) (by norm_num) hL.1 hL.2 (by norm_num)
    hlog.1 hlog.2 endpoint_series_n_lower endpoint_series_n_upper
  constructor <;> linarith

lemma log_endpoint_div_e :
    Real.log (1490000000000/Real.exp 1) = Real.log 1490000000000-1 := by
  rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1),Real.log_exp]

lemma li_endpoint_div_e_bounds {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    (21092171547:ℝ) ≤ li (1490000000000/Real.exp 1) ∧
      li (1490000000000/Real.exp 1) ≤ 21092171550 := by
  have hL := log_endpoint_bounds
  have hlog := log_log_coarse (by linarith [hL.1] : 27 ≤ Real.log 1490000000000-1)
    (by linarith [hL.2] : Real.log 1490000000000-1 ≤ 29)
  have hx : 1 < (1490000000000:ℝ)/Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).mpr
    have he := Real.exp_one_lt_d9
    linarith
  have h := li_from_series hseries (x:=1490000000000/Real.exp 1) (llo:=3) (lhi:=4)
    (a:=(270297972358859/10000000000000:ℝ))
    (b:=(270297972358860/10000000000000:ℝ))
    hx (by norm_num) (by rw [log_endpoint_div_e]; linarith [hL.1])
    (by rw [log_endpoint_div_e]; linarith [hL.2]) (by norm_num)
    (by simpa only [log_endpoint_div_e] using hlog.1)
    (by simpa only [log_endpoint_div_e] using hlog.2)
    endpoint_series_ne_lower endpoint_series_ne_upper
  constructor <;> linarith

noncomputable def upperPi (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  li x+3-(1/20:ℝ)*Real.sqrt x/Real.log x

noncomputable def improvedEnvelope (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  li (x/Real.exp 1)-(1061/500:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1)-
    (upperPi li x)^2*Real.log x/(Real.exp 1*x)

lemma sqrt_endpoint_bounds :
    (1220655:ℝ) ≤ Real.sqrt 1490000000000 ∧
      Real.sqrt 1490000000000 ≤ 1220656 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
  · apply Real.sqrt_le_iff.mpr
    norm_num

lemma sqrt_endpoint_div_e_upper :
    Real.sqrt (1490000000000/Real.exp 1) ≤ 740366 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have he := Real.exp_one_gt_d9
  nlinarith

/-- The improved analytic envelope at the new transition has a strict margin
larger than 90. All finite Taylor and rational arithmetic is proved above in
the kernel. The sole identity input is the explicitly named DLMF series law. -/
theorem improved_endpoint_positive {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) :
    90 < improvedEnvelope li 1490000000000 := by
  let Llo : ℝ := 280297972358859/10000000000000
  let Lhi : ℝ := 280297972358860/10000000000000
  let U : ℝ := 55206531504-1220655/(20*Lhi)
  have hL := log_endpoint_bounds
  change Llo ≤ Real.log 1490000000000 ∧ Real.log 1490000000000 ≤ Lhi at hL
  have hli := li_endpoint_bounds hseries
  have hliE := li_endpoint_div_e_bounds hseries
  have hr := sqrt_endpoint_bounds
  have hrE := sqrt_endpoint_div_e_upper
  have hlogpos : 0 < Real.log (1490000000000:ℝ) := Real.log_pos (by norm_num)
  have hrootTerm : (1220655:ℝ)/(20*Lhi) ≤
      (1/20:ℝ)*Real.sqrt 1490000000000/Real.log 1490000000000 := by
    calc
      _ ≤ Real.sqrt 1490000000000/(20*Real.log 1490000000000) :=
        div_le_div₀ (by norm_num) hr.1 (by positivity) (by linarith [hL.2])
      _ = _ := by ring
  have hU : upperPi li 1490000000000 ≤ U := by
    unfold upperPi
    dsimp [U]
    linarith [hli.2]
  have hrootTermUp : (1/20:ℝ)*Real.sqrt 1490000000000/Real.log 1490000000000 ≤ 100000 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hLp : (27:ℝ) ≤ Real.log 1490000000000 := by dsimp [Llo] at hL; linarith [hL.1]
    nlinarith [hr.2]
  have hUpos : 0 ≤ upperPi li 1490000000000 := by
    unfold upperPi
    linarith [hli.1]
  have hU0 : 0 ≤ U := hUpos.trans hU
  have hUsq : (upperPi li 1490000000000)^2 ≤ U^2 := pow_le_pow_left₀ hUpos hU 2
  have hT : (1061/500:ℝ)*Real.sqrt (1490000000000/Real.exp 1)/(Real.log 1490000000000-1) ≤
      (1061/500:ℝ)*740366/(Llo-1) := by
    apply div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hrE (by norm_num)) (by dsimp [Llo]; norm_num)
    linarith [hL.1]
  have hE : (27182818283/10000000000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hW : (upperPi li 1490000000000)^2*Real.log 1490000000000/(Real.exp 1*1490000000000) ≤
      U^2*Lhi/((27182818283/10000000000:ℝ)*1490000000000) := by
    apply div_le_div₀ (by positivity)
      (mul_le_mul hUsq hL.2 hlogpos.le (sq_nonneg U)) (by norm_num)
    nlinarith [hE]
  have hnum : 90 < (21092171547:ℝ)-(1061/500:ℝ)*740366/(Llo-1)-
      U^2*Lhi/((27182818283/10000000000:ℝ)*1490000000000) := by
    dsimp [Llo,Lhi,U]
    norm_num
  unfold improvedEnvelope
  linarith [hliE.1]

#print axioms improved_endpoint_positive

/-- The derivative identity is an ordinary, prime-free analytic fact. In the
final glue it can be supplied from the separately stated li-offset identity. -/
def LogIntegralDerivative (li : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 2 < x → HasDerivAt li (1/Real.log x) x

lemma li_exp_four_upper {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    li (Real.exp 4) ≤ 21 := by
  have hlog4 : Real.log (4:ℝ) ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [log_two_decimal.2]
  have he : (1:ℝ) < Real.exp 4 := by simpa using Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 4)
  have h := li_from_series hseries (x:=Real.exp 4) (a:=4) (b:=4)
    (llo:=0) (lhi:=2) (slo:=0) (shi:=18)
    he (by norm_num) (by simp) (by simp) (by norm_num)
    (by simpa using Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))
    (by simpa using hlog4)
    (by unfold eiPartial; exact Finset.sum_nonneg (fun n _ => eiTerm_nonneg (by norm_num) n))
    (by norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial])
  linarith [h.2]

/-- A convenient elementary li upper barrier, obtained by actual differentiation,
not imported as an oracle bound. -/
theorem li_upper_barrier {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    (hderiv : LogIntegralDerivative li) {x : ℝ} (hx : Real.exp 4 ≤ x) :
    li x ≤ x/(Real.log x-2) := by
  let f : ℝ → ℝ := fun t => t/(Real.log t-2)-li t
  have he4 : (42:ℝ) ≤ Real.exp 4 := by
    have he : (27/10:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he 4
    norm_num [← Real.exp_nat_mul] at hp
    linarith
  have hd : ∀ t ∈ Ici (Real.exp 4),
      HasDerivAt f ((Real.log t-4)/(Real.log t*(Real.log t-2)^2)) t := by
    intro t ht
    have ht2 : 2 < t := by linarith [ht.out]
    have ht0 : 0 < t := by linarith
    have hL : 4 ≤ Real.log t := by
      apply (Real.le_log_iff_exp_le ht0).mpr
      exact ht
    have hLn : Real.log t ≠ 0 := by linarith
    have hden : Real.log t-2 ≠ 0 := by linarith
    have hd := ((hasDerivAt_id t).div ((Real.hasDerivAt_log ht0.ne').sub_const 2) hden).sub (hderiv t ht2)
    have hv : (1*(Real.log t-2)-t*t⁻¹)/(Real.log t-2)^2-1/Real.log t =
        (Real.log t-4)/(Real.log t*(Real.log t-2)^2) := by
      field_simp
      <;> ring
    rw [show id t = t from rfl,hv] at hd
    convert! hd using 1 <;> rfl
  have hm : MonotoneOn f (Ici (Real.exp 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      have ht0 : 0 < t := by have h:=interior_subset ht; linarith [h.out]
      have hL : 4 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr (interior_subset ht)
      positivity
  have hb : 0 ≤ f (Real.exp 4) := by
    dsimp [f]
    rw [Real.log_exp]
    have hli := li_exp_four_upper hseries
    linarith
  have hh := hm (show Real.exp 4 ∈ Ici (Real.exp 4) by simp) hx hx
  dsimp [f] at hh
  linarith

#print axioms li_upper_barrier

/-- A uniform numerical height inequality derived from the tangent lower
bound for exp; no finite grid or empirical positivity premise is used. -/
theorem sqrt_height_condition {x : ℝ} (hx : 0 < x) (hL : 28 ≤ Real.log x) :
    (1061/1000:ℝ)*(Real.log x)^4 ≤ Real.sqrt (x/Real.exp 1) := by
  have he27 : (700000:ℝ)^2 ≤ Real.exp 27 := by
    have he : (27182818283/10000000000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27182818283/10000000000) he 27
    norm_num [← Real.exp_nat_mul] at hp
    linarith
  have hehalf : (700000:ℝ) ≤ Real.exp (27/2:ℝ) := by
    have heq : (Real.exp (27/2:ℝ))^2 = Real.exp 27 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp := Real.exp_pos (27/2:ℝ)
    nlinarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hBern : Real.log x/28 ≤ Real.exp ((Real.log x-28)/8) := by
    have ht := Real.add_one_le_exp ((Real.log x-28)/8)
    linarith
  have hpow := pow_le_pow_left₀ (div_nonneg hlog0 (by norm_num)) hBern 4
  have hsmall : (1061/1000:ℝ)*(Real.log x)^4 ≤ 700000*(Real.log x/28)^4 := by
    nlinarith [pow_nonneg hlog0 4]
  have hprod : (1061/1000:ℝ)*(Real.log x)^4 ≤
      Real.exp (27/2:ℝ)*(Real.exp ((Real.log x-28)/8))^4 := by
    calc
      _ ≤ 700000*(Real.log x/28)^4 := hsmall
      _ ≤ Real.exp (27/2:ℝ)*(Real.log x/28)^4 :=
        mul_le_mul_of_nonneg_right hehalf (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
  have hid : Real.exp (27/2:ℝ)*(Real.exp ((Real.log x-28)/8))^4 =
      Real.exp ((Real.log x-1)/2) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [hid] at hprod
  have hs : (Real.exp ((Real.log x-1)/2))^2 = x/Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    have heq : (2:ℝ)*((Real.log x-1)/2) = Real.log x-1 := by ring
    norm_num only [Nat.cast_ofNat]
    rw [heq,Real.exp_sub,Real.exp_log hx]
  have hr := Real.sq_sqrt (show 0 ≤ x/Real.exp 1 by positivity)
  have hp := Real.exp_pos ((Real.log x-1)/2)
  have hsr := Real.sqrt_nonneg (x/Real.exp 1)
  have hsame : Real.exp ((Real.log x-1)/2) = Real.sqrt (x/Real.exp 1) := by nlinarith
  rwa [hsame] at hprod

#print axioms sqrt_height_condition

/-- The lower li estimate used by Axler implies precisely the squared
quantity needed by the corrected derivative formula. -/
lemma squared_numerator_lower {A L x : ℝ} (hx : 0 < x) (hL : 4 ≤ L)
    (hA : x/(L-1-1/L) < A) :
    x/(L*(L-1)) ≤ A*(L-1)-x := by
  have hL0 : 0 < L := by linarith
  have hm : 0 < L-1 := by linarith
  have hinv : 1/L ≤ 1 := (div_le_one hL0).mpr (by linarith)
  have hd : 0 < L-1-1/L := by linarith
  have hAp : 0 < A := (div_pos hx hd).trans hA
  have hxA := (div_lt_iff₀ hd).mp hA
  have hdist : A/L < A*(L-1)-x := by
    have heq : A*(L-1-1/L) = A*(L-1)-A/L := by ring
    linarith
  have hweak : x/(L-1) < A := by
    apply (div_lt_iff₀ hm).mpr
    have hpos : 0 < A/L := div_pos hAp hL0
    linarith
  have hdiv := div_lt_div_of_pos_right hweak hL0
  have heq : x/(L-1)/L = x/(L*(L-1)) := by field_simp <;> ring
  rw [heq] at hdiv
  exact (hdiv.trans hdist).le

/-- Pure ordered-field part of Axler's derivative argument, with the corrected
squared li term. -/
lemma base_derivative_nonneg {A L x E s : ℝ} (hx : 0 < x) (hE : 0 < E)
    (hL : 4 ≤ L) (hs : 0 < s)
    (hA : x/(L-1-1/L) < A)
    (hheight : (1061/1000:ℝ)*L^4 ≤ s) :
    0 ≤ (A*(L-1)-x)^2/(E*x^2*(L-1))-
      (1061/1000:ℝ)*(L-3)/(E*(L-1)^2*s) := by
  have hL0 : 0 < L := by linarith
  have hm : 0 < L-1 := by linarith
  let B : ℝ := 1/(E*L^2*(L-1)^3)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnum := squared_numerator_lower hx hL hA
  have hnum2 : x ≤ (A*(L-1)-x)*(L*(L-1)) := (div_le_iff₀ (mul_pos hL0 hm)).mp hnum
  have hratio : 1 ≤ (A*(L-1)-x)*L*(L-1)/x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [hnum2]
  have hrpow : 1 ≤ ((A*(L-1)-x)*L*(L-1)/x)^2 := by nlinarith [sq_nonneg ((A*(L-1)-x)*L*(L-1)/x-1)]
  have hfirst : B ≤ (A*(L-1)-x)^2/(E*x^2*(L-1)) := by
    calc
      B = 1*B := by ring
      _ ≤ ((A*(L-1)-x)*L*(L-1)/x)^2*B := mul_le_mul_of_nonneg_right hrpow hB
      _ = _ := by dsimp [B]; field_simp <;> ring
  have hpoly : L^2*(L-1)*(L-3) ≤ L^4 := by
    have hp : 0 ≤ L^2*(4*L-3) := mul_nonneg (sq_nonneg L) (by linarith)
    nlinarith
  have hn : (1061/1000:ℝ)*L^2*(L-1)*(L-3) ≤ s := by
    have hp := mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ) ≤ 1061/1000)
    nlinarith
  have hratio2 : (1061/1000:ℝ)*L^2*(L-1)*(L-3)/s ≤ 1 := (div_le_one hs).mpr hn
  have hsecond : (1061/1000:ℝ)*(L-3)/(E*(L-1)^2*s) ≤ B := by
    calc
      _ = ((1061/1000:ℝ)*L^2*(L-1)*(L-3)/s)*B := by dsimp [B]; field_simp <;> ring
      _ ≤ 1*B := mul_le_mul_of_nonneg_right hratio2 hB
      _ = B := by ring
  linarith

#print axioms base_derivative_nonneg

noncomputable def baseEnvelope (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  li (x/Real.exp 1)-(1061/500:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1)-
    (li x)^2*Real.log x/(Real.exp 1*x)

noncomputable def baseDerivative (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  (li x*(Real.log x-1)-x)^2/(Real.exp 1*x^2*(Real.log x-1))-
    (1061/1000:ℝ)*(Real.log x-3)/(Real.exp 1*(Real.log x-1)^2*Real.sqrt (x/Real.exp 1))

lemma baseEnvelope_hasDerivAt {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {x : ℝ} (hx : 6 < x) (hL : 1 < Real.log x) :
    HasDerivAt (baseEnvelope li) (baseDerivative li x) x := by
  have hx0 : 0 < x := by linarith
  have hE := Real.exp_pos 1
  have hxe : 2 < x/Real.exp 1 := by
    apply (lt_div_iff₀ hE).mpr
    linarith [Real.exp_one_lt_d9]
  have hln : Real.log x ≠ 0 := by linarith
  have hm : Real.log x-1 ≠ 0 := by linarith
  have hroot : 0 < Real.sqrt (x/Real.exp 1) := Real.sqrt_pos.mpr (by positivity)
  have hlogxe : Real.log (x/Real.exp 1) = Real.log x-1 := by
    rw [Real.log_div hx0.ne' hE.ne',Real.log_exp]
  have hs := ((hasDerivAt_id x).div_const (Real.exp 1)).sqrt (show x/Real.exp 1 ≠ 0 by positivity)
  have ha := (hderiv (x/Real.exp 1) hxe).comp x ((hasDerivAt_id x).div_const (Real.exp 1))
  have ht := ((hs.const_mul (1061/500:ℝ)).div ((Real.hasDerivAt_log hx0.ne').sub_const 1) hm)
  have hu := (((hderiv x (by linarith)).pow 2).mul (Real.hasDerivAt_log hx0.ne')).div
    ((hasDerivAt_id x).const_mul (Real.exp 1)) (by positivity)
  have hd := (ha.sub ht).sub hu
  have hsq : Real.exp 1*(Real.sqrt (x/Real.exp 1))^2 = x := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  convert! hd using 1
  dsimp [baseDerivative]
  rw [hlogxe]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  generalize hAv : li x = A
  generalize hLv : Real.log x = L
  generalize hSv : Real.sqrt (x/Real.exp 1) = s
  rw [hSv] at hsq hroot
  rw [hLv] at hL
  rw [← hsq]
  field_simp [show L ≠ 0 by linarith,show L-1 ≠ 0 by linarith]
  <;> ring

#print axioms baseEnvelope_hasDerivAt

noncomputable def gainPart (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  (li x+3)/(10*Real.sqrt x)-6*li x*Real.log x/x-1/(400*Real.log x)-9*Real.log x/x

noncomputable def gainDerivative (li : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2*x/Real.log x-li x-3)/(20*x*Real.sqrt x)+
    6*(li x*(Real.log x-1)-x)/x^2+
    1/(400*x*(Real.log x)^2)+9*(Real.log x-1)/x^2

lemma gainPart_hasDerivAt {li : ℝ → ℝ} (hderiv : LogIntegralDerivative li)
    {x : ℝ} (hx : 2 < x) (hL : 1 < Real.log x) :
    HasDerivAt (gainPart li) (gainDerivative li x) x := by
  have hx0 : 0 < x := by linarith
  have hLn : Real.log x ≠ 0 := by linarith
  have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hA := hderiv x hx
  have hlog := Real.hasDerivAt_log hx0.ne'
  have hs := Real.hasDerivAt_sqrt hx0.ne'
  have h1 := (hA.add_const 3).div (hs.const_mul 10) (by positivity)
  have h2 := (((hA.mul hlog).div (hasDerivAt_id x) hx0.ne').const_mul 6)
  have h3 := (hasDerivAt_const x (1:ℝ)).div (hlog.const_mul 400) (by positivity)
  have h4 := (hlog.const_mul 9).div (hasDerivAt_id x) hx0.ne'
  have hd := ((h1.sub h2).sub h3).sub h4
  have hsq := Real.sq_sqrt hx0.le
  convert! hd using 1
  · ext t
    dsimp [gainPart]
    ring
  · dsimp [gainDerivative]
    generalize hAv : li x = A
    generalize hLv : Real.log x = L
    generalize hSv : Real.sqrt x = s
    rw [hSv] at hsq hroot
    rw [hLv] at hL
    rw [← hsq]
    field_simp [show L ≠ 0 by linarith]
    <;> ring

lemma improved_eq_base_add_gain {li : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hL : 0 < Real.log x) :
    improvedEnvelope li x = baseEnvelope li x+gainPart li x/Real.exp 1 := by
  have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq := Real.sq_sqrt hx.le
  unfold improvedEnvelope baseEnvelope gainPart upperPi
  generalize hAv : li x = A
  generalize hLv : Real.log x = L
  generalize hSv : Real.sqrt x = s
  rw [hSv] at hsq hroot
  rw [hLv] at hL
  rw [← hsq]
  field_simp
  <;> ring

#print axioms gainPart_hasDerivAt
#print axioms improved_eq_base_add_gain

lemma endpoint_domain_exp_four : Real.exp 4 ≤ (1490000000000:ℝ) := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
  norm_num [← Real.exp_nat_mul] at hp
  linarith

lemma log_finite_upper {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 10000000000000000000) :
    Real.log x ≤ 44 := by
  apply (Real.log_le_iff_le_exp hx0).mpr
  have he : (27182818283/10000000000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27182818283/10000000000) he 44
  norm_num [← Real.exp_nat_mul] at hp
  linarith

lemma gain_derivative_nonneg {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    (hderiv : LogIntegralDerivative li) {x : ℝ} (hx : (1490000000000:ℝ) ≤ x)
    (hxhi : x ≤ 10000000000000000000)
    (hA : x/(Real.log x-1-1/Real.log x) < li x) :
    0 ≤ gainDerivative li x := by
  have hx0 : 0 < x := by linarith
  have hL : 28 ≤ Real.log x := by
    have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 1490000000000) hx
    linarith [log_endpoint_bounds.1]
  have hLhi := log_finite_upper hx0 hxhi
  have hL0 : 0 < Real.log x := by linarith
  have hm : 0 < Real.log x-2 := by linarith
  have hliup := li_upper_barrier hseries hderiv (endpoint_domain_exp_four.trans hx)
  have hW : (3:ℝ) ≤ x*(Real.log x-4)/(Real.log x*(Real.log x-2)) := by
    apply (le_div_iff₀ (mul_pos hL0 hm)).mpr
    have hden : Real.log x*(Real.log x-2) ≤ (1848:ℝ) := by
      have hp := mul_le_mul hLhi (by linarith : Real.log x-2 ≤ 42)
        (by linarith : 0 ≤ Real.log x-2) (by norm_num : (0:ℝ) ≤ 44)
      norm_num at hp
      exact hp
    have hnum : 24*x ≤ x*(Real.log x-4) := by
      nlinarith [mul_nonneg hx0.le (show 0 ≤ Real.log x-28 by linarith)]
    nlinarith
  have hid : 2*x/Real.log x-x/(Real.log x-2) =
      x*(Real.log x-4)/(Real.log x*(Real.log x-2)) := by field_simp <;> ring
  have hfirst : 0 ≤ 2*x/Real.log x-li x-3 := by linarith
  have hN := squared_numerator_lower hx0 (by linarith : 4 ≤ Real.log x) hA
  have hN0 : 0 ≤ li x*(Real.log x-1)-x :=
    (div_nonneg hx0.le (mul_nonneg hL0.le (by linarith))).trans hN
  have hm1 : 0 ≤ Real.log x-1 := by linarith
  unfold gainDerivative
  exact add_nonneg (add_nonneg
    (add_nonneg (div_nonneg hfirst (by positivity)) (div_nonneg (mul_nonneg (by norm_num) hN0) (sq_nonneg x)))
    (by positivity)) (by positivity)

#print axioms gain_derivative_nonneg

/-- Exact finite-domain source obligation recovered from Axler's pi lower
estimate and Büthe's pi<li result, not Ramanujan positivity. -/
def AxlerLiLower (li : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
    x/(Real.log x-1-1/Real.log x) < li x

/-- The improved envelope is monotone on the full closed analytic bridge. -/
theorem improvedEnvelope_monotone {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    (hlower : AxlerLiLower li) :
    MonotoneOn (improvedEnvelope li) (Icc (1490000000000:ℝ) 10000000000000000000) := by
  have hd : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
      HasDerivAt (improvedEnvelope li)
        (baseDerivative li x+gainDerivative li x/Real.exp 1) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 1 < x := by linarith [hx.1]
    have hL : 28 ≤ Real.log x := by
      have ht := Real.log_le_log (by norm_num : (0:ℝ) < 1490000000000) hx.1
      linarith [log_endpoint_bounds.1]
    have hb := baseEnvelope_hasDerivAt hderiv (by linarith [hx.1] : 6 < x) (by linarith : 1 < Real.log x)
    have hg := gainPart_hasDerivAt hderiv (by linarith [hx.1] : 2 < x) (by linarith : 1 < Real.log x)
    have hc := hb.add (hg.div_const (Real.exp 1))
    apply hc.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx1] with t ht
    change 1 < t at ht
    exact improved_eq_base_add_gain (by linarith : 0 < t) (Real.log_pos ht)
  have hdpos : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
      0 ≤ baseDerivative li x+gainDerivative li x/Real.exp 1 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hL : 28 ≤ Real.log x := by
      have ht := Real.log_le_log (by norm_num : (0:ℝ) < 1490000000000) hx.1
      linarith [log_endpoint_bounds.1]
    have hb := base_derivative_nonneg hx0 (Real.exp_pos 1) (by linarith : 4 ≤ Real.log x)
      (Real.sqrt_pos.mpr (by positivity) : 0 < Real.sqrt (x/Real.exp 1))
      (hlower x hx) (sqrt_height_condition hx0 hL)
    change 0 ≤ baseDerivative li x at hb
    have hg := gain_derivative_nonneg hseries hderiv hx.1 hx.2 (hlower x hx)
    exact add_nonneg hb (div_nonneg hg (Real.exp_pos 1).le)
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hdpos x (interior_subset hx)

/-- The whole closed bridge inherits the kernel-checked endpoint margin. -/
theorem improvedEnvelope_margin {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    (hlower : AxlerLiLower li) {x : ℝ}
    (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    90 < improvedEnvelope li x := by
  have hm := improvedEnvelope_monotone hseries hderiv hlower
  exact (improved_endpoint_positive hseries).trans_le
    (hm (by norm_num) hx hx.1)

/-- Mathematical transport from the actual source-derived pi enclosures. The
numerical positivity required here is supplied, not assumed, by the preceding theorem. -/
theorem ramanujan_on_analytic_bridge {pi li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    (hlower : AxlerLiLower li)
    (hpi0 : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000, 0 ≤ pi x)
    (hpiU : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000, pi x ≤ upperPi li x)
    (hpiL : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
      li (x/Real.exp 1)-(1061/500:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1) ≤ pi (x/Real.exp 1))
    {x : ℝ} (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    (pi x)^2 < Real.exp 1*x/Real.log x*pi (x/Real.exp 1) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : 1 < x := by linarith [hx.1]
  have hL := Real.log_pos hx1
  have hR := improvedEnvelope_margin hseries hderiv hlower hx
  have hU0 := (hpi0 x hx).trans (hpiU x hx)
  have hsq := pow_le_pow_left₀ (hpi0 x hx) (hpiU x hx) 2
  have hterm : (pi x)^2*Real.log x/(Real.exp 1*x) ≤
      (upperPi li x)^2*Real.log x/(Real.exp 1*x) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hL.le) (by positivity)
  have hlow := hpiL x hx
  unfold improvedEnvelope at hR
  have hg : (pi x)^2*Real.log x/(Real.exp 1*x) < pi (x/Real.exp 1) := by linarith
  have hg2 := (div_lt_iff₀ (show 0 < Real.exp 1*x by positivity)).mp hg
  rw [show Real.exp 1*x/Real.log x*pi (x/Real.exp 1) =
    Real.exp 1*x*pi (x/Real.exp 1)/Real.log x by ring]
  apply (lt_div_iff₀ hL).mpr
  nlinarith

#print axioms improvedEnvelope_monotone
#print axioms improvedEnvelope_margin
#print axioms ramanujan_on_analytic_bridge

lemma buthe_coefficient_le {L : ℝ} (hL : 27 ≤ L) :
    (39/20:ℝ)+(39/10:ℝ)/L+(39/2:ℝ)/L^2 ≤ 1061/500 := by
  have hL0 : 0 < L := by linarith
  have h1 : (39/10:ℝ)/L ≤ (39/10:ℝ)/27 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have hsq : (27:ℝ)^2 ≤ L^2 := pow_le_pow_left₀ (by norm_num) hL 2
  have h2 : (39/2:ℝ)/L^2 ≤ (39/2:ℝ)/(27:ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  norm_num at h1 h2 ⊢
  linarith

/-- Original Büthe-v2 pi lower contract, with its complete domain and final
version's constants. This is a literature-supported analytic input, not a new
computation claimed as verified here. -/
def ButhePiLower (pi li : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (2:ℝ) 10000000000000000000,
    li t-Real.sqrt t/Real.log t*((39/20:ℝ)+(39/10:ℝ)/Real.log t+(39/2:ℝ)/(Real.log t)^2) ≤ pi t

/-- Source-exact Büthe lower pi bounds supply the numerical input used by the
new analytic bridge; no new prime-count data are introduced. -/
theorem buthe_lower_supplies_bridge {pi li : ℝ → ℝ} (hbuthe : ButhePiLower pi li)
    {x : ℝ} (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    li (x/Real.exp 1)-(1061/500:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1) ≤ pi (x/Real.exp 1) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hE := Real.exp_pos 1
  have hxe : 2 ≤ x/Real.exp 1 := by
    apply (le_div_iff₀ hE).mpr
    linarith [hx.1,Real.exp_one_lt_d9]
  have hxeU : x/Real.exp 1 ≤ (10000000000000000000:ℝ) := by
    apply (div_le_iff₀ hE).mpr
    have he := Real.exp_one_gt_two
    nlinarith [hx.2]
  have hlogid : Real.log (x/Real.exp 1) = Real.log x-1 := by
    rw [Real.log_div hx0.ne' hE.ne',Real.log_exp]
  have hlog : 27 ≤ Real.log (x/Real.exp 1) := by
    rw [hlogid]
    have hmon := Real.log_le_log (by norm_num : (0:ℝ) < 1490000000000) hx.1
    linarith [log_endpoint_bounds.1]
  have hcoef := buthe_coefficient_le hlog
  have hp := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ Real.sqrt (x/Real.exp 1)/Real.log (x/Real.exp 1) by positivity)
  have hb := hbuthe (x/Real.exp 1) ⟨hxe,hxeU⟩
  rw [hlogid] at hb hp
  have heq : Real.sqrt (x/Real.exp 1)/(Real.log x-1)*(1061/500:ℝ) =
      (1061/500:ℝ)*Real.sqrt (x/Real.exp 1)/(Real.log x-1) := by ring
  rw [heq] at hp
  linarith

/-- Exact import adapter from the two published source statements used by
Axler. It does not change their constants or endpoints. -/
theorem axler_lower_supplies_li {pi li : ℝ → ℝ}
    (hAxler : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000,
      x/(Real.log x-1-1/Real.log x) < pi x)
    (hButhe : ∀ x ∈ Icc (1490000000000:ℝ) 10000000000000000000, pi x < li x) :
    AxlerLiLower li := by
  intro x hx
  exact (hAxler x hx).trans (hButhe x hx)

#print axioms buthe_lower_supplies_bridge
#print axioms axler_lower_supplies_li

/-- Sharp tail required by the actual twenty-cell atanh evaluator in
`c/generate_finite.cpp`. In particular the factor `41` is retained. -/
theorem log_atanh20_error {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ logAtanhError 20 r ∧
      logAtanhError 20 r ≤ 2*r^41/(41*(1-r^2)) := by
  let f : ℝ → ℝ := fun t => 2*t^40/(1-t^2)
  let g : ℝ → ℝ := fun t => 2*t^40/(1-r^2)
  let H : ℝ → ℝ := fun t => 2*t^41/(41*(1-r^2))
  have hdr : 0 < 1-r^2 := by nlinarith
  have hden : ∀ t ∈ Icc (0:ℝ) r, 0 < 1-t^2 := by
    intro t ht
    nlinarith [ht.1,ht.2]
  have hfc : ContinuousOn f (Icc 0 r) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (hden t ht).ne'
  have hgc : ContinuousOn g (Icc 0 r) := by unfold g; fun_prop
  have hfi : IntervalIntegrable f volume 0 r := hfc.intervalIntegrable_of_Icc hr
  have hgi : IntervalIntegrable g volume 0 r := hgc.intervalIntegrable_of_Icc hr
  have hfd : ∀ t ∈ uIcc (0:ℝ) r,
      HasDerivAt (logAtanhError 20) (f t) t := by
    intro t ht
    rw [uIcc_of_le hr] at ht
    have ht0 : -(1:ℝ) < t := by linarith [ht.1]
    have ht1 : t < 1 := by linarith [ht.2]
    simpa [f] using logAtanhError_deriv ht0 ht1 20
  have hgd : ∀ t ∈ uIcc (0:ℝ) r, HasDerivAt H (g t) t := by
    intro t ht
    have hd := (((hasDerivAt_id t).pow 41).const_mul 2).div_const (41*(1-r^2))
    convert! hd using 1
    dsimp [g]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub]
    field_simp
    <;> ring
  have hfe := intervalIntegral.integral_eq_sub_of_hasDerivAt hfd hfi
  have hge := intervalIntegral.integral_eq_sub_of_hasDerivAt hgd hgi
  have hz : logAtanhError 20 0 = 0 := by simp [logAtanhError,logAtanhPoly]
  have hzH : H 0 = 0 := by simp [H]
  rw [hz,sub_zero] at hfe
  rw [hzH,sub_zero] at hge
  have hfn : ∀ t ∈ Icc (0:ℝ) r, 0 ≤ f t := by
    intro t ht
    exact div_nonneg (by positivity) (hden t ht).le
  have hfg : ∀ t ∈ Icc (0:ℝ) r, f t ≤ g t := by
    intro t ht
    have hp : t^2 ≤ r^2 := pow_le_pow_left₀ ht.1 ht.2 2
    exact div_le_div_of_nonneg_left (by positivity) hdr (by linarith)
  have hlo := intervalIntegral.integral_nonneg (μ:=volume) hr hfn
  have hhi := intervalIntegral.integral_mono_on hr hfi hgi hfg
  rw [hfe] at hlo hhi
  rw [hge] at hhi
  exact ⟨hlo,hhi⟩

theorem log_atanh20_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log ((1+r)/(1-r)) ≤ logAtanhPoly 20 r+2*r^41/(41*(1-r^2)) := by
  have h := log_atanh20_error hr hr1
  have hp : (1+r:ℝ) ≠ 0 := by linarith
  have hm : (1-r:ℝ) ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  unfold logAtanhError at h
  linarith

/-- Exact integer constant produced by the factorial loop in the finite program. -/
def finiteELow : ℕ := ∑ k ∈ range 21, (2^60:ℕ)/Nat.factorial k

def eLoopTerm : ℕ → ℕ
  | 0 => 2^60
  | n+1 => eLoopTerm n/(n+1)

lemma eLoopTerm_eq (n : ℕ) : eLoopTerm n = (2^60:ℕ)/Nat.factorial n := by
  induction n with
  | zero => simp [eLoopTerm]
  | succ n ih =>
    rw [eLoopTerm,ih,Nat.factorial_succ,Nat.div_div_eq_div_mul]
    congr 1
    ring

lemma finiteELow_value : finiteELow = 3133965575612453533 := by
  norm_num [finiteELow,Finset.sum_range_succ,Nat.factorial]

/-- Actual real e belongs to the exact fixed-point window used by the source.
The near-20 theorem is a Mathlib kernel proof; no native evaluation is used. -/
theorem finite_e_enclosure :
    (finiteELow:ℝ)/(2:ℝ)^60 ≤ Real.exp 1 ∧
      Real.exp 1 ≤ ((finiteELow+22:ℕ):ℝ)/(2:ℝ)^60 := by
  have h := abs_le.mp Real.exp_one_near_20
  rw [finiteELow_value]
  constructor <;> norm_num <;> linarith [h.1,h.2]

#print axioms log_atanh20_error
#print axioms log_atanh20_upper
#print axioms finite_e_enclosure

/-- Büthe final Theorem2(1.10), with its actual real domain. -/
def ButhePiBelowLi : Prop :=
  ∀ t ∈ Icc (2:ℝ) 10000000000000000000, IEANTN.primeCounting t < IEANTN.li t

/-- Büthe final Theorem2(1.7), used in a weakened non-strict form. -/
def ButheThetaDeficit : Prop :=
  ∀ t ∈ Icc (2:ℝ) 10000000000000000000,
    Chebyshev.theta t-t ≤ -(1/20:ℝ)*Real.sqrt t

/-- Axler2016Cor3.5, lasttablecolumn. Its explicit literature computation
remains part of this named analytic source input. -/
def AxlerPiLower : Prop :=
  ∀ t : ℝ, 468049 ≤ t → t/(Real.log t-1-1/Real.log t) < IEANTN.primeCounting t

/-- The new real-domain analytic continuation for the actual IEANTN prime
counting function. All analytic source assumptions are named, and no finite
Ramanujan positivity or external endpoint calculation is assumed. -/
theorem actual_ramanujan_analytic_bridge
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : RamanujanPV.Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi) (htheta : ButheThetaDeficit)
    (hlower : AxlerPiLower)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    {x : ℝ} (hx : x ∈ Icc (1490000000000:ℝ) 10000000000000000000) :
    RamanujanPV.Holds x := by
  have hd : LogIntegralDerivative IEANTN.li := by
    intro t ht
    exact RamanujanPV.LiBarriers.actual_li_hasDerivAt hoffset ht
  have hA : AxlerLiLower IEANTN.li := by
    apply axler_lower_supplies_li (pi:=IEANTN.primeCounting)
    · intro t ht
      exact hlower t (by linarith [ht.1])
    · intro t ht
      exact hpositive t ⟨by linarith [ht.1],ht.2⟩
  have hli2 : 0 ≤ IEANTN.li 2 :=
    (RamanujanPV.primeCounting_nonneg 2).trans (hpositive 2 (by norm_num)).le
  have hlog2 : (2/3:ℝ) ≤ Real.log 2 := by linarith [log_two_decimal.1]
  apply ramanujan_on_analytic_bridge hseries hd hA
  · intro t ht
    exact RamanujanPV.primeCounting_nonneg t
  · intro t ht
    have h := RamanujanPV.Middle.pi_upper_from_theta_deficit
      (x:=t) (α:=(1/20:ℝ)) (by linarith [ht.1]) (by norm_num)
      (fun u hu hut => htheta u ⟨hu,hut.trans ht.2⟩) hoffset hli2 hlog2
    exact h
  · intro t ht
    exact buthe_lower_supplies_bridge hbuthe ht
  · exact hx

#print axioms actual_ramanujan_analytic_bridge

/-- A coarse but kernel-proved li(2) upper bound, sufficient for the ten-term
factorial barriers used by the intermediate continuation. -/
theorem li_two_upper {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) : li 2 ≤ 2 := by
  have hlog := log_two_decimal
  have hlo : (2/3:ℝ) ≤ Real.log 2 := by linarith [hlog.1]
  have hhi : Real.log 2 ≤ (7/10:ℝ) := by linarith [hlog.2]
  have hloglog : Real.log (Real.log (2:ℝ)) ≤ 0 := by
    apply Real.log_nonpos
    · linarith
    · linarith
  have h := li_from_series hseries (x:=2) (a:=(2/3:ℝ)) (b:=(7/10:ℝ))
    (llo:=Real.log (Real.log (2:ℝ))) (lhi:=0) (slo:=0) (shi:=1)
    (by norm_num) (by norm_num) hlo hhi (by norm_num) le_rfl hloglog
    (by unfold eiPartial; exact Finset.sum_nonneg (fun n _ => eiTerm_nonneg (by norm_num) n))
    (by norm_num [eiPartial,eiTerm,Finset.sum_range_succ,Nat.factorial])
  linarith [h.2]

/-- Mathematics-side correspondence for the exact ceildiv expression in C.
This theorem is not by itself a source-to-AST execution proof. -/
def sourceCeilDiv (a b : ℕ) : ℕ := a/b + if a%b = 0 then 0 else 1

lemma sourceCeilDiv_mul_ge (a : ℕ) {b : ℕ} (hb : 0 < b) :
    a ≤ sourceCeilDiv a b*b := by
  have hdiv := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  unfold sourceCeilDiv
  split_ifs with hzero
  · simp only [Nat.add_zero]
    nlinarith [hdiv]
  · have hp : 1 ≤ a%b := Nat.one_le_iff_ne_zero.mpr hzero
    nlinarith

lemma sourceCeilDiv_real (a : ℕ) {b : ℕ} (hb : 0 < b) :
    (a:ℝ)/(b:ℝ) ≤ (sourceCeilDiv a b:ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ) < b)).mpr
  exact_mod_cast sourceCeilDiv_mul_ge a hb

lemma ceil_mul_scaled (a b : ℕ) {F : ℕ} (hF : 0 < F) :
    ((a:ℝ)/F)*((b:ℝ)/F) ≤ (sourceCeilDiv (a*b) F:ℝ)/F := by
  have h := div_le_div_of_nonneg_right (sourceCeilDiv_real (a*b) hF)
    (show (0:ℝ) ≤ F by positivity)
  push_cast at h
  convert! h using 1 <;> field_simp <;> ring

/-- The exact unbounded-integer mathematical loop corresponding to the C
power updates. Machine-width applicability is a separate execution obligation. -/
def log20Power (F z z2 : ℕ) : ℕ → ℕ
  | 0 => z
  | k+1 => sourceCeilDiv (log20Power F z z2 k*z2) F

lemma log20Power_dominates {F z z2 : ℕ} (hF : 0 < F) {r : ℝ}
    (hr : 0 ≤ r) (hz : r ≤ (z:ℝ)/F) (hz2 : r^2 ≤ (z2:ℝ)/F) (k : ℕ) :
    r^(2*k+1) ≤ (log20Power F z z2 k:ℝ)/F := by
  induction k with
  | zero => simpa [log20Power] using hz
  | succ k ih =>
    have hmul := mul_le_mul ih hz2 (sq_nonneg r)
      (show (0:ℝ) ≤ (log20Power F z z2 k:ℝ)/F by positivity)
    have hround := ceil_mul_scaled (log20Power F z z2 k) z2 hF
    have heq : r^(2*(k+1)+1) = r^(2*k+1)*r^2 := by
      rw [show 2*(k+1)+1 = (2*k+1)+2 by omega,pow_add]
    rw [heq]
    exact hmul.trans hround

/-- The directed real upper form consumed by the rounded logarithm loop. -/
theorem log20_directed_upper {r z2 power sum output : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hz2 : r^2 ≤ z2) (hz21 : z2 < 1)
    (hpower : r^41 ≤ power) (hsum : logAtanhPoly 20 r ≤ 2*sum)
    (hout : 2*sum+2*power/(41*(1-z2)) ≤ output) :
    Real.log ((1+r)/(1-r)) ≤ output := by
  have ht := log_atanh20_upper hr hr1
  have hdz : 0 < 1-z2 := by linarith
  have hpower0 : 0 ≤ power := (pow_nonneg hr 41).trans hpower
  have htail : 2*r^41/(41*(1-r^2)) ≤ 2*power/(41*(1-z2)) := by
    apply div_le_div₀ (by positivity) (by linarith [hpower]) (by positivity)
    linarith [hz2]
  linarith

#print axioms li_two_upper
#print axioms log20Power_dominates
#print axioms log20_directed_upper

def log20Sum (F z z2 : ℕ) : ℕ :=
  ∑ k ∈ range 20, sourceCeilDiv (log20Power F z z2 k) (2*k+1)

def log20Output (F z z2 : ℕ) : ℕ :=
  2*log20Sum F z z2 + sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2))

lemma log20Sum_dominates {F z z2 : ℕ} (hF : 0 < F) {r : ℝ}
    (hr : 0 ≤ r) (hz : r ≤ (z:ℝ)/F) (hz2 : r^2 ≤ (z2:ℝ)/F) :
    logAtanhPoly 20 r ≤ 2*((log20Sum F z z2:ℝ)/F) := by
  have hterm : ∀ k : ℕ, r^(2*k+1)/(2*k+1:ℕ) ≤
      (sourceCeilDiv (log20Power F z z2 k) (2*k+1):ℝ)/F := by
    intro k
    have hp := log20Power_dominates hF hr hz hz2 k
    have h1 := div_le_div_of_nonneg_right hp
      (show (0:ℝ) ≤ (2*k+1:ℕ) by positivity)
    have h2 := div_le_div_of_nonneg_right
      (sourceCeilDiv_real (log20Power F z z2 k) (by omega : 0 < 2*k+1))
      (show (0:ℝ) ≤ F by positivity)
    have heq : ((log20Power F z z2 k:ℝ)/F)/(2*k+1:ℕ) =
        ((log20Power F z z2 k:ℝ)/(2*k+1:ℕ))/F := by ring
    rw [heq] at h1
    exact h1.trans h2
  have hsum := Finset.sum_le_sum (s:=range 20) (fun k _ => hterm k)
  have hsid : (∑ k ∈ range 20,
      (sourceCeilDiv (log20Power F z z2 k) (2*k+1):ℝ)/F) =
      (log20Sum F z z2:ℝ)/F := by
    rw [← Finset.sum_div]
    unfold log20Sum
    norm_cast
  rw [hsid] at hsum
  calc
    logAtanhPoly 20 r = 2*∑ k ∈ range 20, r^(2*k+1)/(2*k+1:ℕ) := by
      unfold logAtanhPoly
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

lemma log20Tail_dominates {F z z2 : ℕ} (hF : 0 < F) (hz2 : z2 < F) :
    2*((log20Power F z z2 20:ℝ)/F)/(41*(1-(z2:ℝ)/F)) ≤
      (sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2)):ℝ)/F := by
  have hden : 0 < 41*(F-z2) := Nat.mul_pos (by norm_num) (Nat.sub_pos_of_lt hz2)
  have h := div_le_div_of_nonneg_right
    (sourceCeilDiv_real (2*log20Power F z z2 20*F) hden)
    (show (0:ℝ) ≤ F by positivity)
  push_cast [Nat.cast_sub hz2.le] at h
  convert! h using 1
  field_simp
  <;> ring

/-- The complete twenty-step integer numerical algorithm has a valid real
logarithm upper bound. It matches the mathematical operations of the actual C
loop; source/AST identity, machine widths and execution remain separate. -/
theorem log20Output_sound {F z z2 : ℕ} (hF : 0 < F) (hz21 : z2 < F) {r : ℝ}
    (hr : 0 ≤ r) (hz : r ≤ (z:ℝ)/F) (hz2 : r^2 ≤ (z2:ℝ)/F) :
    Real.log ((1+r)/(1-r)) ≤ (log20Output F z z2:ℝ)/F := by
  have hF0 : (0:ℝ) < F := by exact_mod_cast hF
  have hzr : (z2:ℝ)/F < 1 := (div_lt_one hF0).mpr (by exact_mod_cast hz21)
  have hr1 : r < 1 := by nlinarith [sq_nonneg r]
  apply log20_directed_upper hr hr1 hz2 hzr
    (log20Power_dominates hF hr hz hz2 20) (log20Sum_dominates hF hr hz hz2)
  have ht := log20Tail_dominates (z:=z) hF hz21
  unfold log20Output
  push_cast
  convert! add_le_add_left ht (2*((log20Sum F z z2:ℝ)/F)) using 1 <;> ring

#print axioms log20Output_sound

lemma sourceCeilDiv_le {a b q : ℕ} (hb : 0 < b) (ha : a ≤ q*b) :
    sourceCeilDiv a b ≤ q := by
  have hdiv := Nat.div_add_mod a b
  unfold sourceCeilDiv
  split_ifs with hzero
  · simp only [Nat.add_zero]
    by_contra! hq
    have hh : q+1 ≤ a/b := by omega
    nlinarith [hdiv]
  · have hmod : 0 < a%b := Nat.pos_of_ne_zero hzero
    have hq : a/b < q := by
      by_contra! hh
      nlinarith [hdiv]
    omega

def fixedLogZ (num den : ℕ) : ℕ := sourceCeilDiv ((2^60)*num) den

def fixedLogZ2 (num den : ℕ) : ℕ := sourceCeilDiv ((fixedLogZ num den)^2) (2^60)

def fixedLogSeries (num den : ℕ) : ℕ := log20Output (2^60) (fixedLogZ num den) (fixedLogZ2 num den)

/-- The integer preprocessing of the actual source maintains a positive
remainder denominator, uniformly over every admissible rational argument. -/
lemma fixedLogZ2_lt {num den : ℕ} (hd : 0 < den) (hhalf : 2*num ≤ den) :
    fixedLogZ2 num den < 2^60 := by
  have hz : fixedLogZ num den ≤ 2^59 := by
    apply sourceCeilDiv_le hd
    norm_num
    nlinarith [hhalf]
  have hz2 : fixedLogZ2 num den ≤ 2^59 := by
    apply sourceCeilDiv_le (by norm_num : 0 < (2^60:ℕ))
    nlinarith [hz]
  exact hz2.trans_lt (by norm_num)

/-- The actual rational-input twenty-term directed algorithm is sound as
unbounded integer mathematics. A source execution proof must still establish
its agreement with the compiled width-checked C operations. -/
theorem fixedLogSeries_sound {num den : ℕ} (hd : 0 < den) (hhalf : 2*num ≤ den) :
    Real.log ((1+(num:ℝ)/den)/(1-(num:ℝ)/den)) ≤ (fixedLogSeries num den:ℝ)/(2:ℝ)^60 := by
  have hF : 0 < (2^60:ℕ) := by norm_num
  have hr : (0:ℝ) ≤ (num:ℝ)/den := by positivity
  have hz : (num:ℝ)/den ≤ (fixedLogZ num den:ℝ)/(2^60:ℕ) := by
    have h := div_le_div_of_nonneg_right
      (sourceCeilDiv_real ((2^60)*num) hd) (show (0:ℝ) ≤ (2^60:ℕ) by positivity)
    push_cast at h
    convert! h using 1 <;> norm_num [fixedLogZ] <;> field_simp <;> ring
  have hz2 : ((num:ℝ)/den)^2 ≤ (fixedLogZ2 num den:ℝ)/(2^60:ℕ) := by
    have hp := pow_le_pow_left₀ hr hz 2
    have hh := ceil_mul_scaled (fixedLogZ num den) (fixedLogZ num den) hF
    have hid : (fixedLogZ num den*fixedLogZ num den) = (fixedLogZ num den)^2 := by ring
    rw [hid] at hh
    have hhs : ((fixedLogZ num den:ℝ)/(2^60:ℕ))^2 ≤
        (fixedLogZ2 num den:ℝ)/(2^60:ℕ) := by simpa [fixedLogZ2,pow_two] using hh
    exact hp.trans hhs
  have h := log20Output_sound hF (fixedLogZ2_lt hd hhalf) hr hz hz2
  simpa only [fixedLogSeries,Nat.cast_pow,Nat.cast_ofNat] using h

#print axioms fixedLogSeries_sound

/-- Integer result of the exact binary-normalization wrapper in `log_upper`.
The arguments `two,k` are the final states of the source normalization loop. -/
def binaryLogUpper (n two k : ℕ) : ℕ :=
  sourceCeilDiv (k*fixedLogSeries 1 3+fixedLogSeries (n-two) (n+two)) (2^20)

/-- The complete mathematical counterpart of `log_upper(n)`, with its actual
2^40 output scale. The source loop must establish the explicit binary-state
invariants; they are not assumptions about the logarithm or the final result. -/
theorem binaryLogUpper_sound {n two k : ℕ} (hpow : two = 2^k)
    (hlow : two ≤ n) (hhigh : n < 2*two) :
    Real.log (n:ℝ) ≤ (binaryLogUpper n two k:ℝ)/(2:ℝ)^40 := by
  have htwo : 0 < two := by rw [hpow]; positivity
  have hn : 0 < n := htwo.trans_le hlow
  have hden : 0 < n+two := by omega
  have hhalf : 2*(n-two) ≤ n+two := by omega
  have hm := fixedLogSeries_sound hden hhalf
  have htwo0 : (0:ℝ) < two := by exact_mod_cast htwo
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hid : (1+(n-two:ℕ)/(n+two:ℕ):ℝ)/(1-(n-two:ℕ)/(n+two:ℕ)) = (n:ℝ)/two := by
    push_cast [Nat.cast_sub hlow]
    field_simp [htwo0.ne']
    <;> ring
  rw [hid] at hm
  have h2 := fixedLogSeries_sound (by norm_num : 0 < (3:ℕ)) (by norm_num : 2*(1:ℕ) ≤ 3)
  norm_num at h2
  have h2' : Real.log 2 ≤ (fixedLogSeries 1 3:ℝ)/(2:ℝ)^60 := by norm_num; exact h2
  have hlogtwo : Real.log (two:ℝ) = (k:ℝ)*Real.log 2 := by
    have hp : (two:ℝ) = (2:ℝ)^k := by exact_mod_cast hpow
    rw [hp,Real.log_pow]
  have hlogn : Real.log (n:ℝ) = (k:ℝ)*Real.log 2+Real.log ((n:ℝ)/two) := by
    rw [Real.log_div hn0.ne' htwo0.ne',hlogtwo]
    ring
  have hmain : Real.log (n:ℝ) ≤
      ((k*fixedLogSeries 1 3+fixedLogSeries (n-two) (n+two):ℕ):ℝ)/(2:ℝ)^60 := by
    calc
      _ = (k:ℝ)*Real.log 2+Real.log ((n:ℝ)/two) := hlogn
      _ ≤ (k:ℝ)*((fixedLogSeries 1 3:ℝ)/(2:ℝ)^60)+
          (fixedLogSeries (n-two) (n+two):ℝ)/(2:ℝ)^60 :=
        add_le_add (mul_le_mul_of_nonneg_left h2' (by positivity)) hm
      _ = _ := by push_cast; ring
  have hround := div_le_div_of_nonneg_right
    (sourceCeilDiv_real (k*fixedLogSeries 1 3+fixedLogSeries (n-two) (n+two))
      (by norm_num : 0 < (2^20:ℕ)))
    (show (0:ℝ) ≤ (2:ℝ)^40 by positivity)
  have hround2 : ((k*fixedLogSeries 1 3+fixedLogSeries (n-two) (n+two):ℕ):ℝ)/(2:ℝ)^60 ≤
      (binaryLogUpper n two k:ℝ)/(2:ℝ)^40 := by
    convert! hround using 1 <;> norm_num [binaryLogUpper] <;> field_simp <;> ring
  exact hmain.trans hround2

#print axioms binaryLogUpper_sound
end RamanujanPV.AnalyticTransition
