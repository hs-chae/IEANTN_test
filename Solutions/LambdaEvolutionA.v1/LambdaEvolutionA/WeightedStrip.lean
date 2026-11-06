/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ZeroWeights
/-! The CH2 all-strip weight uniformly for the weighted parameter0≤σ<1.
This extends the existing σ=0 proof; the endpointσ=1 is taken only by a
proved limit, since cTS has a singular displayed expression there. -/
namespace LambdaEvolutionA
open Complex Real Set MeasureTheory CH2QRH
set_option maxHeartbeats 0

lemma scaled_point_shift {T b γ σ : ℝ} (hT : 0 < T) :
    (((b : ℂ) + (γ : ℂ)*I) - σ) / (I*T) =
      ((γ/T : ℝ) : ℂ) + (((σ-b)/T : ℝ) : ℂ)*I := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- Uniform CH2 spectral weight on the genuine approach domain0≤σ<1. -/
theorem weighted_strip_bound (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {T b γ ξ σ : ℝ} (hT : 1000 ≤ T) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hγ0 : 0 < γ) (hγT : γ < T) (hξ : |ξ| ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ‖CH2Section6.omegaPlus T σ ((b : ℂ) + (γ : ℂ)*I)
        + (ξ : ℂ)*I*CH2Section6.thetaTS T 1 ((b : ℂ) + (γ : ℂ)*I)‖
      ≤ T/(Real.pi*γ)+2 := by
  have hT0 : 0<T := by linarith
  have hu0 : 0<γ/T := div_pos hγ0 hT0
  have hu1 : γ/T<1 := (div_lt_one hT0).mpr hγT
  have hsub : |σ-b|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |((σ-b)/T : ℝ)|≤1/T := by
    rw [abs_div,abs_of_pos hT0]
    exact div_le_div_of_nonneg_right hsub hT0.le
  have hFc := norm_Fc_vertical_le hcs hu0 hu1 hT hy
  have he : 1/(Real.pi*(γ/T))=T/(Real.pi*γ) := by field_simp
  rw [he] at hFc
  have hc : ‖CH2Section6.cTS T σ-1/(Real.pi:ℂ)‖≤1/T := by
    apply (CH2Section6.norm_cTS_sub_le hT0 hσ1.ne).trans
    apply div_le_div_of_nonneg_right _ hT0.le
    rw [abs_of_nonpos (by linarith : σ-1≤0)]
    linarith
  have hreal : ‖((ξ*(1-b)/T:ℝ):ℂ)‖≤1/T := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,
      abs_of_nonneg (by linarith : 0≤1-b),abs_of_pos hT0]
    have hm : |ξ| *(1-b)≤1 := by nlinarith [abs_nonneg ξ]
    exact div_le_div_of_nonneg_right hm hT0.le
  have himag : ‖(ξ:ℂ)*((1-γ/T:ℝ):ℂ)*I‖≤1 := by
    rw [norm_mul,norm_mul,norm_I,mul_one,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤1-γ/T)]
    nlinarith [abs_nonneg ξ]
  have htheta := norm_add_le ((ξ:ℂ)*((1-γ/T:ℝ):ℂ)*I) (((ξ*(1-b)/T:ℝ):ℂ))
  have hsum := norm_add_le
    (CH2Section7.Fc (((γ/T:ℝ):ℂ)+(((σ-b)/T:ℝ):ℂ)*I))
    (CH2Section6.cTS T σ-1/(Real.pi:ℂ))
  have hsum2 := norm_add_le
    (CH2Section7.Fc (((γ/T:ℝ):ℂ)+(((σ-b)/T:ℝ):ℂ)*I)+(CH2Section6.cTS T σ-1/(Real.pi:ℂ)))
    ((ξ:ℂ)*((1-γ/T:ℝ):ℂ)*I+(((ξ*(1-b)/T:ℝ):ℂ)))
  rw [CH2Section6.omegaPlus_eq_Fc,scaled_point_shift hT0,theta_factor hT0]
  have hiT : 1/T≤(1/1000:ℝ) := one_div_le_one_div_of_le (by norm_num) hT
  linarith
#print axioms weighted_strip_bound
end LambdaEvolutionA
