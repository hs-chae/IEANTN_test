/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BoxFourierCoefficients
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
namespace RHOcticPush.BoxFourierSeries
open Real Complex Set MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def sineCoeff (n : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (fun y : ℝ => (Real.sin y : ℂ)) n
noncomputable def cosineCoeff (n : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (fun y : ℝ => (Real.cos y : ℂ)) n

lemma sineCoeff_nonzero (n : ℤ) (hn : n≠0) :
    sineCoeff n = -2 / ((Real.pi : ℂ) * (4*(n:ℂ)^2-1)) := by
  have hs := fourierCoeffOn_of_hasDerivAt_Ioo Real.pi_pos hn
    (f:=fun y : ℝ => (Real.sin y:ℂ))
    (f':=fun y : ℝ => (Real.cos y:ℂ))
    (by fun_prop) (fun y _ => (Real.hasDerivAt_sin y).ofReal_comp)
    ((by fun_prop : Continuous (fun y : ℝ => (Real.cos y:ℂ))).intervalIntegrable 0 Real.pi)
  have hc := fourierCoeffOn_of_hasDerivAt_Ioo Real.pi_pos hn
    (f:=fun y : ℝ => (Real.cos y:ℂ))
    (f':=fun y : ℝ => (-(Real.sin y:ℂ)))
    (by fun_prop) (fun y _ => by simpa using (Real.hasDerivAt_cos y).ofReal_comp)
    ((by fun_prop : Continuous (fun y : ℝ => (-(Real.sin y:ℂ)))).intervalIntegrable 0 Real.pi)
  have hneg : fourierCoeffOn Real.pi_pos (fun y : ℝ => (-(Real.sin y:ℂ))) n =
      -sineCoeff n := by
    simpa [sineCoeff] using
      fourierCoeffOn.const_mul (fun y : ℝ => (Real.sin y:ℂ)) (-1) n Real.pi_pos
  simp only [Real.sin_pi,Real.sin_zero,Real.cos_pi,Real.cos_zero,
    Complex.ofReal_zero,Complex.ofReal_neg,Complex.ofReal_one,
    sub_zero,zero_sub,mul_zero,sub_self] at hs hc
  rw [hneg] at hc
  change sineCoeff n = 1/(-2*(Real.pi:ℂ)*I*n)*(-((Real.pi:ℂ)*cosineCoeff n)) at hs
  simp only [fourier_coe_apply,Complex.ofReal_zero,mul_zero,zero_div,
    Complex.exp_zero,one_mul] at hc
  have hc' : cosineCoeff n = 1/(-2*(Real.pi:ℂ)*I*n)*
      (-2+(Real.pi:ℂ)*sineCoeff n) := by
    convert hc using 1 <;> first | rfl | ring
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
  have hd : (4*(n:ℂ)^2-1)≠0 := by
    exact_mod_cast (show (4*n^2-1:ℤ)≠0 by omega)
  rw [hc'] at hs
  apply (eq_div_iff (mul_ne_zero hp hd)).mpr
  field_simp [hp,hnC,Complex.I_ne_zero] at hs
  norm_num [Complex.I_sq] at hs
  linear_combination -hs

lemma sineCoeff_zero : sineCoeff 0=(2:ℂ)/Real.pi := by
  simp only [sineCoeff,fourierCoeffOn_eq_integral,sub_zero,neg_zero,
    fourier_zero,one_smul,intervalIntegral.integral_ofReal,integral_sin]
  norm_num [smul_eq_mul,Complex.real_smul] <;> ring

noncomputable def coefficient (n : ℤ) : ℂ :=
  ((-2 / (Real.pi * (4*(n:ℝ)^2-1)) : ℝ) : ℂ)

lemma sineCoeff_eq (n : ℤ) : sineCoeff n=coefficient n := by
  by_cases hn : n=0
  · subst n
    simp [coefficient,sineCoeff_zero]
  · rw [sineCoeff_nonzero n hn]
    simp only [coefficient,Complex.ofReal_div,Complex.ofReal_neg,
      Complex.ofReal_ofNat,Complex.ofReal_mul,Complex.ofReal_sub,
      Complex.ofReal_pow,Complex.ofReal_intCast,Complex.ofReal_one]

lemma absSin_periodic : Function.Periodic (fun x : ℝ => ((|Real.sin x|:ℝ):ℂ)) Real.pi := by
  intro x
  simp only [Real.sin_add_pi,abs_neg]

noncomputable def circleAbsSin : C(AddCircle Real.pi,ℂ) where
  toFun := absSin_periodic.lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (by fun_prop : Continuous (fun x : ℝ => ((|Real.sin x|:ℝ):ℂ))).quotient_liftOn' _

lemma circleAbsSin_coe (x : ℝ) : circleAbsSin (x:AddCircle Real.pi)=((|Real.sin x|:ℝ):ℂ) := rfl

local instance : Fact (0<Real.pi) := ⟨Real.pi_pos⟩

lemma actual_coefficient (n : ℤ) : fourierCoeff circleAbsSin n=coefficient n := by
  rw [←sineCoeff_eq n,sineCoeff,fourierCoeff_eq_intervalIntegral _ _ 0,
    fourierCoeffOn_eq_integral]
  simp only [zero_add,sub_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le Real.pi_pos.le] at hy
  dsimp only
  rw [circleAbsSin_coe,abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hy)]
  simp only [fourier_coe_apply,sub_zero]

lemma coefficients_summable : Summable coefficient := by
  apply Summable.of_norm_bounded_eventually
    (((Real.summable_one_div_int_pow (p:=2)).mpr (by norm_num)).mul_left (2/Real.pi))
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  have hni : (1:ℤ)≤n^2 := by have := sq_pos_of_ne_zero hn; omega
  have hsq : (1:ℝ)≤(n:ℝ)^2 := by exact_mod_cast hni
  have hd : 0<4*(n:ℝ)^2-1 := by nlinarith
  rw [coefficient,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_neg,
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_mul,
    abs_of_pos Real.pi_pos,abs_of_pos hd]
  have h := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤2/Real.pi)
    (by nlinarith : (0:ℝ)<(n:ℝ)^2) (by nlinarith : (n:ℝ)^2≤4*(n:ℝ)^2-1)
  convert h using 1 <;> first | rfl | simp only [div_div,mul_one_div]

/-- The complete, absolutely convergent Fourier expansion of the ACTUAL |sin|,
valid at every real point, with exact two-sided integer coefficients. -/
theorem full_absolute_sine_series (x : ℝ) :
    HasSum (fun n : ℤ => coefficient n • fourier n (x:AddCircle Real.pi))
      ((|Real.sin x|:ℝ):ℂ) := by
  have hc : Summable (fourierCoeff circleAbsSin) :=
    coefficients_summable.congr (fun n => (actual_coefficient n).symm)
  simpa only [actual_coefficient,circleAbsSin_coe] using
    has_pointwise_sum_fourier_series_of_summable hc (x:AddCircle Real.pi)

/-- Convergence in the continuous-map norm, hence uniform on the whole circle. -/
theorem uniform_absolute_sine_series :
    HasSum (fun n : ℤ => coefficient n • (fourier n : C(AddCircle Real.pi,ℂ))) circleAbsSin := by
  have hc : Summable (fourierCoeff circleAbsSin) :=
    coefficients_summable.congr (fun n => (actual_coefficient n).symm)
  simpa only [actual_coefficient] using hasSum_fourier_series_of_summable hc

lemma phase_real (n : ℤ) (x : ℝ) :
    (fourier n (x:AddCircle Real.pi)).re=Real.cos (2*(n:ℝ)*x) := by
  rw [fourier_coe_apply]
  have he : (2*(Real.pi:ℂ)*I*n*x/Real.pi)=((2*(n:ℝ)*x:ℝ):ℂ)*I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  rw [he,Complex.exp_ofReal_mul_I_re]

noncomputable def realTerm (x : ℝ) (n : ℤ) : ℝ :=
  (-2/(Real.pi*(4*(n:ℝ)^2-1)))*Real.cos (2*(n:ℝ)*x)

lemma full_real_series (x : ℝ) : HasSum (realTerm x) |Real.sin x| := by
  have hr := Complex.hasSum_re (full_absolute_sine_series x)
  convert hr using 1
  · funext n
    simp only [realTerm,coefficient,smul_eq_mul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase_real]
  · rfl

/-- Exact one-sided real cosine expansion, with no missing negative frequencies. -/
theorem absolute_sine_cosine_series (x : ℝ) :
    |Real.sin x|=2/Real.pi-(4/Real.pi)*
      ∑' n : ℕ+, Real.cos (2*(n:ℝ)*x)/(4*(n:ℝ)^2-1) := by
  have hs := full_real_series x
  have he : (realTerm x).Even := by
    intro n
    simp only [realTerm,Int.cast_neg,neg_sq]
    rw [show 2*(-(n:ℝ))*x=-(2*(n:ℝ)*x) by ring,Real.cos_neg]
  have hi := tsum_int_eq_zero_add_two_mul_tsum_pnat he hs.summable
  have ht : (∑' n : ℕ+, realTerm x n)=
      (-2/Real.pi)*(∑' n : ℕ+, Real.cos (2*(n:ℝ)*x)/(4*(n:ℝ)^2-1)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [realTerm]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hs.tsum_eq,ht] at hi
  norm_num [realTerm] at hi
  linear_combination hi

noncomputable def weight (n : ℕ+) : ℝ := 1/(4*(n:ℝ)^2-1)

lemma denominator_pos (n : ℕ+) : 0<4*(n:ℝ)^2-1 := by
  have hn : (1:ℝ)≤n := by exact_mod_cast n.property
  nlinarith

lemma weights_summable : Summable weight := by
  have hn := (Real.summable_one_div_nat_pow (p:=2)).mpr (by norm_num)
  have hp : Summable (fun n : ℕ+ => 1/(n:ℝ)^2) := hn.subtype (fun n : ℕ => 0<n)
  apply Summable.of_nonneg_of_le (fun n => by exact div_nonneg (by norm_num) (denominator_pos n).le) _ hp
  intro n
  have hn : (1:ℝ)≤n := by exact_mod_cast n.property
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

lemma cosine_terms_summable (x : ℝ) :
    Summable (fun n : ℕ+ => Real.cos (2*(n:ℝ)*x)/(4*(n:ℝ)^2-1)) := by
  apply Summable.of_norm_bounded weights_summable
  intro n
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (denominator_pos n)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (denominator_pos n).le

lemma weights_sum : (∑' n : ℕ+,weight n)=(1/2:ℝ) := by
  have h := absolute_sine_cosine_series 0
  norm_num only [mul_zero,Real.cos_zero,Real.sin_zero,abs_zero] at h
  change (0:ℝ)=2/Real.pi-(4/Real.pi)*∑' n : ℕ+,weight n at h
  field_simp [Real.pi_ne_zero] at h
  linarith

/-- Nonnegative form: this is the full identity suitable for Tonelli/Mellin
interchange, rather than a merely formal term-by-term oscillatory integral. -/
theorem absolute_sine_positive_series (x : ℝ) :
    |Real.sin x|=(4/Real.pi)*
      ∑' n : ℕ+, (1-Real.cos (2*(n:ℝ)*x))/(4*(n:ℝ)^2-1) := by
  have he : (fun n : ℕ+ => (1-Real.cos (2*(n:ℝ)*x))/(4*(n:ℝ)^2-1))=
      fun n => weight n-Real.cos (2*(n:ℝ)*x)/(4*(n:ℝ)^2-1) := by
    funext n
    simp only [weight,sub_div]
  rw [he,weights_summable.tsum_sub (cosine_terms_summable x),weights_sum]
  have h := absolute_sine_cosine_series x
  linear_combination h

lemma positive_series_nonneg (x : ℝ) (n : ℕ+) :
    0≤(1-Real.cos (2*(n:ℝ)*x))/(4*(n:ℝ)^2-1) :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (denominator_pos n).le

#print axioms absolute_sine_positive_series
#print axioms uniform_absolute_sine_series
#print axioms absolute_sine_cosine_series
#print axioms sineCoeff_nonzero
#print axioms actual_coefficient
#print axioms coefficients_summable
#print axioms full_absolute_sine_series
end RHOcticPush.BoxFourierSeries
