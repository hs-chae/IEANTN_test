/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Section7Weights
import Section7Zeros
import IEANTN.Vocabulary.ZeroFreeHalfPlane

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The fixed zero-free half-plane bounds every positive-ordinate zero's real part. -/
theorem re_le_boundary {β : ℝ} (hqrh : IEANTN.ZetaZeroFreeHalfPlane β)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : 0 < ρ.im) : ρ.re ≤ β := by
  by_contra h
  have h1 : ρ ≠ 1 := by rintro rfl; simp at him
  exact hqrh ρ (lt_of_not_ge h) h1 hz

/-- Weight an arbitrary nonnegative finite CH2 zero sum using the fixed half-plane.
Finiteness and nonnegative multiplicities are established before comparing the sums. -/
theorem zsum_weight_le {β t x : ℝ} (hqrh : IEANTN.ZetaZeroFreeHalfPlane β)
    (_ht : 0 ≤ t) (hx : 1 ≤ x) (f : ℂ → ℝ)
    (hf : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 t), 0 ≤ f ρ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) (fun ρ ↦ f ρ * x ^ ρ.re)
      ≤ x ^ β * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t) f := by
  classical
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := t) le_rfl
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
  have hm := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hρ'
  have hre := re_le_boundary hqrh hρ'.2.2 hρ'.2.1.1
  have hp := Real.rpow_le_rpow_of_exponent_le hx hre
  calc (f ρ * x ^ ρ.re) * (IEANTN.zetaOrder ρ : ℝ)
      ≤ (f ρ * x ^ β) * (IEANTN.zetaOrder ρ : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hf ρ hρ')) hm
    _ = x ^ β * (f ρ * (IEANTN.zetaOrder ρ : ℝ)) := by ring


/-- Real and imaginary coordinates of the scaled zero, with no RH restriction. -/
theorem scaled_point {T b γ : ℝ} (hT : 0 < T) :
    ((b : ℂ) + (γ : ℂ) * I) / (I * T)
      = ((γ / T : ℝ) : ℂ) + ((-b / T : ℝ) : ℂ) * I := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The theta factor at an arbitrary real part in the critical strip. -/
theorem theta_factor {T b γ ξ : ℝ} (hT : 0 < T) :
    (ξ : ℂ) * I * CH2Section6.thetaTS T 1 ((b : ℂ) + (γ : ℂ) * I)
      = (ξ : ℂ) * ((1 - γ / T : ℝ) : ℂ) * I
        + ((ξ * (1 - b) / T : ℝ) : ℂ) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  unfold CH2Section6.thetaTS
  push_cast
  field_simp
  ring_nf

/-- A uniform small vertical perturbation estimate for the CH2 weight. -/
theorem norm_Fc_vertical_le (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {u y T : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hT : 1000 ≤ T) (hy : |y| ≤ 1 / T) :
    ‖CH2Section7.Fc ((u : ℂ) + (y : ℂ) * I)‖ ≤ 1 / (Real.pi * u) + 3 / 4 := by
  have hT0 : 0 < T := by linarith
  have hp := Real.pi_pos
  have hiT : 1 / T ≤ (1 / 1000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hT
  have hy2 : |y| ≤ 1 / 2 := by linarith
  set z : ℂ := (u : ℂ) + (y : ℂ) * I with hz
  have hun : u ≤ ‖z‖ := by
    have hr := Complex.re_le_norm z
    simpa [hz] using hr
  have hni : ‖1 / ((Real.pi : ℂ) * z)‖ ≤ 1 / (Real.pi * u) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hnz : 0 < ‖z‖ := hu0.trans_le hun
  rcases le_or_gt u (1 / 2) with hu | hu
  · have ha := CH2Section7.sibelius_c hcs hu0 hu hy2
    have hnA : ‖CH2Section7.Acomp z‖ ≤ Real.pi / 3 * u + 1.78 / T := by
      have hsum := norm_add_le (CH2Section7.Acomp z - CH2Section7.Acomp (u : ℂ))
        (CH2Section7.Acomp (u : ℂ))
      rw [sub_add_cancel] at hsum
      have hya : 1.78 * |y| ≤ 1.78 / T := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 1.78)
      linarith [ha.1, ha.2]
    have he : CH2Section7.Fc z = CH2Section7.Acomp z + 1 / ((Real.pi : ℂ) * z) := by
      rw [CH2Section7.Acomp]
      ring
    have hn := norm_add_le (CH2Section7.Acomp z) (1 / ((Real.pi : ℂ) * z))
    rw [he]
    have hnu : Real.pi / 3 * u + 1.78 / T ≤ (3 / 4 : ℝ) := by
      have hp4 := Real.pi_lt_four
      have hyT : 1.78 / T ≤ 1.78 / 1000 := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hiT (by norm_num : (0 : ℝ) ≤ 1.78)
      nlinarith
    linarith
  · have hf := CH2Section7.sibelius_b hcs hu0 hu1 hy2
    have hFc : ‖CH2Section7.Fc (u : ℂ)‖ ≤ 1 / (Real.pi * u) := by
      rw [CH2Section6.Fc_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (CH2Section7.Fweight_pos hu0 hu1)]
      exact (CH2Section7.Fweight_lt_inv hu0 hu1).le
    have hcorr : |y| / (Real.pi * u * ‖z‖) ≤ 4 / (Real.pi * T) := by
      have hd : (0 : ℝ) < Real.pi * u * ‖z‖ := by positivity
      have hprod : (1 : ℝ) ≤ 4 * u * ‖z‖ := by nlinarith
      apply (div_le_iff₀ hd).mpr
      have e : 4 / (Real.pi * T) * (Real.pi * u * ‖z‖)
          = (4 * u * ‖z‖) / T := by field_simp
      rw [e]
      exact (le_div_iff₀ hT0).mpr (((le_div_iff₀ hT0).mp hy).trans hprod)
    have hsmall : 4 / (Real.pi * T) + 1.78 * |y| ≤ (3 / 4 : ℝ) := by
      have hp3 := Real.pi_gt_three
      have h4 : 4 / (Real.pi * T) ≤ 4 / (3 * T) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      have ht4 : 4 / (3 * T) ≤ (4 / 3000 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      nlinarith
    have hn := norm_add_le (CH2Section7.Fc z - CH2Section7.Fc (u : ℂ))
      (CH2Section7.Fc (u : ℂ))
    rw [sub_add_cancel] at hn
    linarith

/-- The all-strip CH2 spectral weight. Unlike the existing critical-line estimate,
this applies at every real part between zero and one. -/
theorem all_strip_weight_bound (hcs : CotangentSeries.v1.cot_series_zeta_values)
    {T b γ ξ : ℝ} (hT : 1000 ≤ T) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hγ0 : 0 < γ) (hγT : γ < T) (hξ : |ξ| ≤ 1) :
    ‖CH2Section6.omegaPlus T 0 ((b : ℂ) + (γ : ℂ) * I)
        + (ξ : ℂ) * I * CH2Section6.thetaTS T 1 ((b : ℂ) + (γ : ℂ) * I)‖
      ≤ T / (Real.pi * γ) + 2 := by
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < γ / T := div_pos hγ0 hT0
  have hu1 : γ / T < 1 := (div_lt_one hT0).mpr hγT
  have hy : |(-b / T : ℝ)| ≤ 1 / T := by
    rw [abs_div, abs_neg, abs_of_nonneg hb0, abs_of_pos hT0]
    exact div_le_div_of_nonneg_right hb1 hT0.le
  have hFc := norm_Fc_vertical_le hcs hu0 hu1 hT hy
  have he : 1 / (Real.pi * (γ / T)) = T / (Real.pi * γ) := by field_simp
  rw [he] at hFc
  have hc : ‖CH2Section6.cTS T 0 - 1 / (Real.pi : ℂ)‖ ≤ 1 / T := by
    simpa using CH2Section6.norm_cTS_sub_le (T := T) (σ := 0) hT0 (by norm_num)
  have hreal : ‖((ξ * (1 - b) / T : ℝ) : ℂ)‖ ≤ 1 / T := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 - b), abs_of_pos hT0]
    have hm : |ξ| * (1 - b) ≤ 1 := by nlinarith [abs_nonneg ξ]
    exact div_le_div_of_nonneg_right hm hT0.le
  have himag : ‖(ξ : ℂ) * ((1 - γ / T : ℝ) : ℂ) * I‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - γ / T)]
    nlinarith [abs_nonneg ξ]
  have htheta := norm_add_le ((ξ : ℂ) * ((1 - γ / T : ℝ) : ℂ) * I)
    (((ξ * (1 - b) / T : ℝ) : ℂ))
  have hsum := norm_add_le
    (CH2Section7.Fc (((γ / T : ℝ) : ℂ) + ((-b / T : ℝ) : ℂ) * I))
    (CH2Section6.cTS T 0 - 1 / (Real.pi : ℂ))
  have hsum2 := norm_add_le
    (CH2Section7.Fc (((γ / T : ℝ) : ℂ) + ((-b / T : ℝ) : ℂ) * I)
      + (CH2Section6.cTS T 0 - 1 / (Real.pi : ℂ)))
    ((ξ : ℂ) * ((1 - γ / T : ℝ) : ℂ) * I + ((ξ * (1 - b) / T : ℝ) : ℂ))
  rw [CH2Section6.omegaPlus_eq_Fc, Complex.ofReal_zero, sub_zero,
    scaled_point hT0, theta_factor hT0]
  have hiT : 1 / T ≤ (1 / 1000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hT
  linarith

end CH2QRH
