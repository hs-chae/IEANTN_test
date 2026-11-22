/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PsiSmoothing
import Mathlib
open Real MeasureTheory Set
namespace RHContinuation.PsiElementary
open PsiSmoothing
set_option maxHeartbeats 2000000

private theorem exp_term {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x^n/(Nat.factorial n : ℝ) ≤ exp x := by
  apply le_trans _ (Real.sum_le_exp_of_nonneg hx (n+1))
  exact Finset.single_le_sum (s := Finset.range (n+1))
    (f := fun k : ℕ => x^k/(Nat.factorial k : ℝ))
    (fun k _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem delta_le_quarter {L : ℝ} (hL : 35 ≤ L) : delta L ≤ 1/4 := by
  have hLp : 0 < L := by linarith
  have he := exp_term (x := L/2) (by positivity) 2
  norm_num at he
  have hprod := mul_nonneg (by linarith [pi_gt_three] : 0 ≤ π-3)
    (exp_nonneg (L/2))
  unfold delta
  rw [(Real.exp_half L).symm]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem main_excess_small {L : ℝ} (hL : 35 ≤ L) :
    4*exp L*(delta L)^2 ≤ sqrt (exp L)/1000 := by
  have hLp : 0 < L := by linarith
  have hs : 0 < sqrt (exp L) := by positivity
  have he := exp_term (x := L/2) (by positivity) 8
  norm_num at he
  have h6 : (35:ℝ)^6 ≤ L^6 := pow_le_pow_left₀ (by norm_num) hL 6
  have hpi : (9:ℝ) ≤ π^2 := by nlinarith [pi_gt_three]
  have h68 : (10321920000:ℝ) ≤ π^2*L^6 := by
    have hm := mul_nonneg (sub_nonneg.mpr hpi) (pow_nonneg hLp.le 6)
    norm_num at h6
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right h68 (sq_nonneg L)
  have hscale : (1000:ℝ)*L^2 ≤ π^2*((L/2)^8/40320) := by
    nlinarith
  have hbig : (1000:ℝ)*L^2 ≤ π^2*sqrt (exp L) := by
    rw [(Real.exp_half L).symm]
    exact hscale.trans (mul_le_mul_of_nonneg_left he (sq_nonneg π))
  have heq : 4*exp L*(delta L)^2 = L^2/π^2 := by
    unfold delta
    nth_rw 1 [show exp L = sqrt (exp L)^2 by rw [Real.sq_sqrt (exp_nonneg L)]]
    field_simp [ne_of_gt hs, pi_ne_zero]
    <;> ring
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos pi_pos)).mpr
  linarith

theorem large_sqrt {L : ℝ} (hL : 35 ≤ L) : (2000:ℝ) ≤ sqrt (exp L) := by
  have he := exp_term (x := L/2) (by linarith) 4
  have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ 35/2 by norm_num)
    (show (35/2:ℝ) ≤ L/2 by linarith) 4
  rw [(Real.exp_half L).symm]
  norm_num at he hp
  linarith

theorem log_two_pi_bounds : 0 ≤ log (2*π) ∧ log (2*π) ≤ 2 := by
  constructor
  · exact log_nonneg (by linarith [pi_gt_three])
  · rw [log_le_iff_le_exp (by positivity)]
    have he := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 by norm_num) 5
    norm_num [Finset.sum_range_succ,Nat.factorial] at he
    linarith [pi_lt_d6]

theorem trivial_bounds {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ PsiSmoothing.trivial t ∧ PsiSmoothing.trivial t ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hsq : (4:ℝ) ≤ t^2 := by nlinarith
  have hpow : t^(-2:ℤ) = 1/t^2 := by simp
  have hz0 : 0 ≤ t^(-2:ℤ) := by rw [hpow]; positivity
  have hz1 : t^(-2:ℤ) ≤ 1/4 := by
    rw [hpow]
    exact one_div_le_one_div_of_le (by norm_num) hsq
  have hy : 0 < 1-t^(-2:ℤ) := by linarith
  have hlo := one_sub_inv_le_log_of_pos hy
  have hhi : log (1-t^(-2:ℤ)) ≤ 0 := log_nonpos hy.le (by linarith)
  have hinv : (1-t^(-2:ℤ))⁻¹ ≤ (4/3:ℝ) := by
    have hh := one_div_le_one_div_of_le
      (show (0:ℝ)<3/4 by norm_num) (show (3/4:ℝ) ≤ 1-t^(-2:ℤ) by linarith)
    norm_num [one_div] at hh ⊢
    exact hh
  unfold PsiSmoothing.trivial
  constructor <;> linarith

theorem trivial_continuousAt {t : ℝ} (ht : 2 ≤ t) : ContinuousAt PsiSmoothing.trivial t := by
  have ht0 : t ≠ 0 := by linarith
  have hne : 1-t^(-2:ℤ) ≠ 0 := by
    have hz : t^(-2:ℤ) ≤ 1/4 := by
      simp only [zpow_neg,zpow_ofNat]
      have hsq : (4:ℝ) ≤ t^2 := by nlinarith
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hsq
    linarith
  unfold PsiSmoothing.trivial
  fun_prop (disch := first | assumption | positivity | exact Or.inl ht0)

theorem shifted_ge_two {L : ℝ} (hL : 35 ≤ L) {s u : ℝ}
    (hs : s = -1 ∨ s = 1) (hu : u ∈ Icc (-1:ℝ) 1) :
    2 ≤ exp L*exp ((s+u)*delta L) := by
  have hd := delta_le_quarter hL
  have hd0 := (PsiSmoothing.delta_pos hL).le
  have hsu : (-2:ℝ) ≤ s+u := by rcases hs with rfl|rfl <;> linarith [hu.1]
  have hm := mul_le_mul_of_nonneg_right hsu hd0
  have he := Real.add_one_le_exp (L+(s+u)*delta L)
  rw [← Real.exp_add]
  linarith

/-- The elementary trivial-zero/constant source obligation is discharged.
No explicit-formula, moment, RH or numerical computation is assumed here. -/
theorem trivial_estimate (k : ℝ → ℝ) (hk : Continuous k)
    (hkn : ∀ u ∈ Icc (-1:ℝ) 1, 0 ≤ k u)
    (hkm : (∫ u in (-1:ℝ)..1, k u) = 1) :
    PsiSmoothing.TrivialTermEstimate k := by
  intro L hL s hs
  have harg : Continuous (fun u : ℝ => exp L*exp ((s+u)*delta L)) := by fun_prop
  have hc : ContinuousOn (fun u : ℝ => k u*PsiSmoothing.trivial
      (exp L*exp ((s+u)*delta L))) (uIcc (-1:ℝ) 1) := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hu
    exact ((hk.continuousAt).mul
      ((trivial_continuousAt (shifted_ge_two hL hs hu)).comp
        (f := fun v : ℝ => exp L*exp ((s+v)*delta L)) (x := u) harg.continuousAt)).continuousWithinAt
  have havg0 : 0 ≤ PsiSmoothing.trivialAverage k s L := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (hkn u hu) (trivial_bounds (shifted_ge_two hL hs hu)).1
  have havg1 : PsiSmoothing.trivialAverage k s L ≤ 1 := by
    unfold PsiSmoothing.trivialAverage
    calc
      (∫ u in (-1:ℝ)..1, k u*PsiSmoothing.trivial
          (exp L*exp ((s+u)*delta L))) ≤ ∫ u in (-1:ℝ)..1, k u := by
        apply intervalIntegral.integral_mono_on (by norm_num) hc.intervalIntegrable
          (hk.intervalIntegrable _ _)
        intro u hu
        have h := mul_le_mul_of_nonneg_left
          (trivial_bounds (shifted_ge_two hL hs hu)).2 (hkn u hu)
        simpa only [mul_one] using h
      _ = 1 := hkm
  have hlog := log_two_pi_bounds
  have hb : |PsiSmoothing.trivialAverage k s L-log (2*π)| ≤ (2:ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hlarge := large_sqrt hL
  calc
    _ ≤ 2 := hb
    _ ≤ sqrt (exp L)*(1/1000) := by linarith

theorem box_trivial : PsiSmoothing.TrivialTermEstimate PsiSmoothing.box :=
  trivial_estimate _ PsiSmoothing.box_continuous PsiSmoothing.box_nonneg PsiSmoothing.box_mass

theorem parabola_trivial : PsiSmoothing.TrivialTermEstimate PsiSmoothing.parabola :=
  trivial_estimate _ PsiSmoothing.parabola_continuous PsiSmoothing.parabola_nonneg
    PsiSmoothing.parabola_mass

/-- Symmetry removes the first-order displacement inside the averaging kernel. -/
theorem main_estimate (k : ℝ → ℝ) (hk : Continuous k)
    (hkn : ∀ u ∈ Icc (-1:ℝ) 1, 0 ≤ k u)
    (hkm : (∫ u in (-1:ℝ)..1, k u) = 1)
    (hfirst : (∫ u in (-1:ℝ)..1, u*k u) = 0) :
    PsiSmoothing.MainTermEstimate k := by
  intro L hL s hs
  let x := exp L
  let d := delta L
  let f : ℝ → ℝ := fun u => k u*(x*(exp ((s+u)*d)-1-(s+u)*d))
  have hx : 0 < x := exp_pos _
  have hd0 : 0 ≤ d := (PsiSmoothing.delta_pos hL).le
  have hd : d ≤ 1/4 := delta_le_quarter hL
  have hcF : Continuous f := by dsimp [f];fun_prop
  have hpoint : ∀ u ∈ Icc (-1:ℝ) 1, |f u| ≤ (4*x*d^2)*k u := by
    intro u hu
    have hsu : |s+u| ≤ 2 := by
      rw [abs_le]
      rcases hs with rfl|rfl <;> constructor <;> linarith [hu.1,hu.2]
    have ht : |(s+u)*d| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg hd0]
      have hm := mul_le_mul_of_nonneg_right hsu hd0
      linarith
    have he := Real.abs_exp_sub_one_sub_id_le ht
    have hsq : ((s+u)*d)^2 ≤ 4*d^2 := by
      have hh : (s+u)^2 ≤ (4:ℝ) := by
        obtain ⟨hl,hu'⟩ := abs_le.mp hsu
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg d)
      nlinarith
    calc
      |f u| = k u*x*|exp ((s+u)*d)-1-(s+u)*d| := by
        dsimp [f]
        rw [abs_mul,abs_mul,abs_of_nonneg (hkn u hu),abs_of_nonneg hx.le]
        ring
      _ ≤ k u*x*((s+u)*d)^2 :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (hkn u hu) hx.le)
      _ ≤ k u*x*(4*d^2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (hkn u hu) hx.le)
      _ = _ := by ring
  have herr : |∫ u in (-1:ℝ)..1, f u| ≤ 4*x*d^2 := by
    calc
      |∫ u in (-1:ℝ)..1, f u| ≤ ∫ u in (-1:ℝ)..1, |f u| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm
            (a := (-1:ℝ)) (b := 1) (f := f) (by norm_num)
      _ ≤ ∫ u in (-1:ℝ)..1, (4*x*d^2)*k u := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hcF.abs.intervalIntegrable _ _)
          ((continuous_const.mul hk).intervalIntegrable _ _) hpoint
      _ = 4*x*d^2 := by rw [intervalIntegral.integral_const_mul,hkm,mul_one]
  have hi1 : IntervalIntegrable
      (fun u : ℝ => k u*(x*exp ((s+u)*d))) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable (fun u : ℝ => x*k u) volume (-1) 1 :=
    (continuous_const.mul hk).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun u : ℝ => (x*d*s)*k u) volume (-1) 1 :=
    (continuous_const.mul hk).intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun u : ℝ => (x*d)*(u*k u)) volume (-1) 1 :=
    (continuous_const.mul (continuous_id.mul hk)).intervalIntegrable _ _
  have hrepr : (∫ u in (-1:ℝ)..1, f u) =
      PsiSmoothing.mainAverage k s L-x-x*d*s := by
    have hf : f = fun u : ℝ => k u*(x*exp ((s+u)*d)) - x*k u -
        (x*d*s)*k u - (x*d)*(u*k u) := by funext u; dsimp [f]; ring
    rw [hf]
    rw [intervalIntegral.integral_sub ((hi1.sub hi2).sub hi3) hi4,
      intervalIntegral.integral_sub (hi1.sub hi2) hi3,
      intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,hkm,hfirst]
    dsimp [PsiSmoothing.mainAverage,x,d]
    ring
  have habss : |s| = (1:ℝ) := by rcases hs with rfl|rfl <;> norm_num
  have hlinear : |x*d*s| = x*d := by
    rw [abs_mul,abs_mul,abs_of_nonneg hx.le,abs_of_nonneg hd0,habss,mul_one]
  have hbound : |PsiSmoothing.mainAverage k s L-x| ≤ 4*x*d^2+x*d := by
    rw [hrepr] at herr
    calc
      |PsiSmoothing.mainAverage k s L-x| =
          |(PsiSmoothing.mainAverage k s L-x-x*d*s)+x*d*s| := by congr 1;ring
      _ ≤ |PsiSmoothing.mainAverage k s L-x-x*d*s|+|x*d*s| := abs_add_le _ _
      _ ≤ _ := by rw [hlinear];linarith
  have hlinear' : x*d = sqrt x*(L/(2*π)) := by
    dsimp [x,d,PsiSmoothing.delta]
    have hsq := Real.sq_sqrt (exp_nonneg L)
    have hsqrt : sqrt (exp L) ≠ 0 := ne_of_gt (by positivity)
    field_simp [hsqrt,pi_ne_zero]
    nlinarith
  have hsmall := main_excess_small hL
  change 4*x*d^2 ≤ sqrt x/1000 at hsmall
  calc
    |PsiSmoothing.mainAverage k s L-exp L| ≤ 4*x*d^2+x*d := hbound
    _ ≤ sqrt x/1000+sqrt x*(L/(2*π)) := by rw [hlinear'];linarith
    _ = sqrt (exp L)*(L/(2*π)+1/1000) := by dsimp [x];ring

theorem box_first_moment : (∫ u in (-1:ℝ)..1, u*PsiSmoothing.box u) = 0 := by
  unfold PsiSmoothing.box
  rw [intervalIntegral.integral_mul_const,integral_id]
  norm_num

theorem parabola_first_moment :
    (∫ u in (-1:ℝ)..1, u*PsiSmoothing.parabola u) = 0 := by
  have hf : (fun u : ℝ => u*PsiSmoothing.parabola u) =
      fun u : ℝ => (3/4:ℝ)*(u-u^3) := by
    funext u
    unfold PsiSmoothing.parabola
    ring
  rw [hf,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub]
  · rw [integral_id,integral_pow]
    norm_num
  · exact continuous_id.intervalIntegrable _ _
  · exact (continuous_id.pow 3).intervalIntegrable _ _

theorem box_main : PsiSmoothing.MainTermEstimate PsiSmoothing.box :=
  main_estimate _ PsiSmoothing.box_continuous PsiSmoothing.box_nonneg
    PsiSmoothing.box_mass box_first_moment

theorem parabola_main : PsiSmoothing.MainTermEstimate PsiSmoothing.parabola :=
  main_estimate _ PsiSmoothing.parabola_continuous PsiSmoothing.parabola_nonneg
    PsiSmoothing.parabola_mass parabola_first_moment

#print axioms main_estimate
#print axioms trivial_estimate
#print axioms main_excess_small
#print axioms trivial_bounds
end RHContinuation.PsiElementary
