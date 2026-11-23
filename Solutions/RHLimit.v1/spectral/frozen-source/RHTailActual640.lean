import FullRH
import RHTailBounds640
import RamAlgebra

namespace Ramanujan640.RHTail
open Real IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640.AnalyticBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def eta (l : ℝ) : ℝ := a*l^2*exp (-l/2)

theorem w_actual_eq (l : ℝ) :
    Ramanujan640.AnalyticBarrier.w IEANTN.li l = RamStudy.w l := by
  unfold Ramanujan640.AnalyticBarrier.w A RamStudy.w
  rw [Real.exp_neg]
  ring

lemma sqrt_exp_div (l : ℝ) : sqrt (exp l)/exp l = exp (-l/2) := by
  have hs : (exp (l/2))^2 = exp l := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have hroot : sqrt (exp l) = exp (l/2) := by
    rw [← hs,Real.sqrt_sq_eq_abs,abs_of_pos (exp_pos _)]
  rw [hroot,← exp_sub]
  congr 1
  ring

lemma exp_large {l : ℝ} (hl : 41 ≤ l) : (2657:ℝ) < exp l := by
  have he : (2:ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0:ℝ)≤2) (by norm_num : (12:ℕ)≠0)
  rw [← exp_nat_mul] at hp
  norm_num at hp
  have hm : exp (12:ℝ) ≤ exp l := exp_le_exp.mpr (by linarith)
  linarith

/-- Source-exact Schoenfeld error on the actual normalized prime count.
The finite-height provider is instantiated separately at each actual x. -/
theorem actual_count_RH_error (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi) {l : ℝ} (hl : 41 ≤ l) :
    |RamStudy.count l-RamStudy.w l| ≤ eta l := by
  have hl0 : 0 ≤ l := by linarith
  have hc : 0 ≤ l/exp l := by positivity
  have hb := FullRH.buthe_all_pi hRH hButhe (x:=exp l) (exp_large hl)
  calc
    |RamStudy.count l-RamStudy.w l| =
        (l/exp l)*|primeCounting (exp l)-li (exp l)| := by
      unfold RamStudy.count RamStudy.w
      rw [← mul_sub,abs_mul,abs_of_nonneg hc]
    _ ≤ (l/exp l)*(sqrt (exp l)*log (exp l)/(8*Real.pi)) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = (1/(8*Real.pi))*l^2*(sqrt (exp l)/exp l) := by rw [log_exp];ring
    _ = eta l := by rw [sqrt_exp_div];rfl

theorem actual_count_RH_bounds (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi) {l : ℝ} (hl : 41 ≤ l) :
    RamStudy.w l-eta l ≤ RamStudy.count l ∧
      RamStudy.count l ≤ RamStudy.w l+eta l := by
  have h := abs_le.mp (actual_count_RH_error hRH hButhe hl)
  constructor <;> linarith

/-- Completed actual-G RH tail, with no desired-bound or numerical-success
premise. The remaining hypotheses are the named standard analytic and
published Schoenfeld/Büthe contracts. -/
theorem actual_RG_tail (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hderiv : LogIntegralDerivative IEANTN.li)
    {l : ℝ} (hl : 42 ≤ l) : (379/1000:ℝ) ≤ RamStudy.RG (exp l) := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlm : l-1 ≠ 0 := by linarith
  let B : ℝ := 1+14/l+145/l^2+1412/l^3-1/1000
  have hbase : B ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
    have h := Ramanujan640.MainTerm.actual_mainterm_lower hseries hderiv (l:=l) (by linarith)
    simpa only [w_actual_eq] using h
  have hb0 : (999/1000:ℝ) ≤ B := by
    have h1 : 0 ≤ 14/l := by positivity
    have h2 : 0 ≤ 145/l^2 := by positivity
    have h3 : 0 ≤ 1412/l^3 := by positivity
    dsimp [B]
    linarith
  have hw : RamStudy.w l ≤ 21/20 := by
    have h := actual_w_tail_upper hseries hderiv hl
    simpa only [w_actual_eq] using h
  have hc := actual_count_RH_bounds hRH hButhe (l:=l) (by linarith)
  have hd := actual_count_RH_bounds hRH hButhe (l:=l-1) (by linarith)
  have hs := RamStudy.signed_consumer hl1 hbase
    (show RamStudy.count l ≤ RamStudy.w l-(-eta l) by linarith [hc.2]) hd.1
  have hsign : B-l^4*(l/(l-1)*eta (l-1))-
      l^4*(2*RamStudy.w l*eta l)-l^4*(eta l)^2 ≤ RamStudy.RG (exp l) := by
    convert! hs using 1 <;> ring
  have hshift : l^4*(l/(l-1)*eta (l-1)) =
      a*l^5*(l-1)*exp ((1-l)/2) := by
    unfold eta
    rw [show -(l-1)/2=(1-l)/2 by ring]
    field_simp [hlm]
    <;> ring
  have hetanonneg : 0 ≤ eta l := by unfold eta;exact mul_nonneg (mul_nonneg a_bounds.1 (sq_nonneg _)) (exp_pos _).le
  have hcross : l^4*(2*RamStudy.w l*eta l) ≤
      (21/10:ℝ)*a*l^6*exp (-l/2) := by
    have h := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*l^4*eta l by positivity)
    dsimp [eta] at h ⊢
    nlinarith
  have hsquare : l^4*(eta l)^2 = a^2*l^8*exp (-l) := by
    have he : exp (-l/2)^2=exp (-l) := by
      rw [← exp_nat_mul]
      congr 1
      ring
    unfold eta
    rw [mul_pow,mul_pow,he]
    ring
  rw [hshift,hsquare] at hsign
  have hD := uniform_D_bound hl
  unfold D at hD
  linarith

theorem actual_RG_tail_one_twentyfifth (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hderiv : LogIntegralDerivative IEANTN.li)
    {l : ℝ} (hl : 42 ≤ l) : (1/25:ℝ) ≤ RamStudy.RG (exp l) :=
  (by norm_num : (1/25:ℝ)≤379/1000).trans (actual_RG_tail hRH hButhe hseries hderiv hl)

#print axioms actual_count_RH_error
#print axioms actual_RG_tail
#print axioms actual_RG_tail_one_twentyfifth
end Ramanujan640.RHTail
