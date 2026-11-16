/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SeparatedHeight

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2Section81

/-- A separated ordinate bounds the local partial fractions without a critical-line hypothesis. -/
theorem saghar_pt_no_RH (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    {t u Δ : ℝ} (ht : 1000 ≤ t) (hu0 : 0 ≤ u) (hu : u ≤ 3 / 2) (hΔ : 0 < Δ)
    (hs : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0)
    (hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im|) :
    ‖deriv riemannZeta (((1 - u : ℝ) : ℂ) + t * I)
        / riemannZeta (((1 - u : ℝ) : ℂ) + t * I)‖
      ≤ (1 / 2 + u) * titchA t +
        ((2 / 5 + 1 / (4 * Real.pi)) * Real.log t + 4.001) +
        (∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ)) / Δ := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hT := titch96A_no_RH hH hrvm hsmall hv (σ := 1 - u) ht
    (by linarith) (by linarith) hs
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4)
    (by linarith)
  rw [zetaZeroesSum_eq_sum_C hfin] at hT
  rw [innerZ_eq hfin]
  set s : ℂ := ((1 - u : ℝ) : ℂ) + t * I with hs_def
  have hS : ‖∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ)‖
      ≤ (∑ ρ ∈ hfin.toFinset, (IEANTN.zetaOrder ρ : ℝ)) / Δ := by
    rw [Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
    have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
    have hm := CH2Section7Z.zetaOrder_nonneg_of_mem
      (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]) hρ'
    have hd : Δ ≤ ‖s - ρ‖ := by
      have hi := Complex.abs_im_le_norm (s - ρ)
      have hie : (s - ρ).im = t - ρ.im := by simp [hs_def]
      rw [hie] at hi
      exact (hfar ρ hρ').trans hi
    rw [norm_mul, norm_zetaOrder_cast hm, norm_div, norm_one,
      div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_left hm hΔ hd
  have hA : (4 * (3 / 2 - (1 - u)) + 1 / 4) / Real.pi * Real.log (t / (2 * Real.pi))
        + (32 * (3 / 2 - (1 - u)) - 1) * (2 / 5 * Real.log t + 4) + 1.5053 + 0.016
      ≤ (1 / 2 + u) * titchA t := by
    have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hLt0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
    have hLt : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
      Real.log_le_log (by positivity) (div_le_self (by linarith) (by linarith))
    have hq : (1 / 4) / Real.pi ≤ 1 / 12 := by rw [div_le_iff₀ hπ]; linarith
    have h1 := mul_le_mul hq hLt hLt0 (by norm_num)
    have e : (4 * (3 / 2 - (1 - u)) + 1 / 4) / Real.pi
        = (1 / 2 + u) * (4 / Real.pi) + (1 / 4) / Real.pi := by ring
    rw [e, titchA]
    nlinarith
  have hd := norm_sub_norm_le (deriv riemannZeta s / riemannZeta s)
    (∑ ρ ∈ hfin.toFinset, 1 / (s - ρ) * (IEANTN.zetaOrder ρ : ℂ))
  change ‖deriv riemannZeta s / riemannZeta s - _‖ ≤ _ at hT
  linarith

/-- Uniform bound for the moderate-real-part part of the horizontal contour. -/
theorem norm_F_le_log_sq (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    {t T u Δ : ℝ} (ht : 1000 ≤ t) (htT : t + 1 / 4 ≤ T)
    (hR : 16 ≤ Real.log T) (hu0 : 0 ≤ u) (hu : u ≤ 3 / 2) (hΔ : 0 < Δ)
    (hΔi : 1 / Δ ≤ 8 * (0.52 * Real.log T + 5))
    (hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im|) :
    ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ ≤ 10 * Real.log T ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hζ : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro hz
    have hzmem : (((1 - u : ℝ) : ℂ) + t * I) ∈
        IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
      ⟨trivial, ⟨by simp, by simp⟩, hz⟩
    have hf := hfar _ hzmem
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, sub_self, abs_zero] at hf
    linarith
  have hF := norm_F_le ht0 hζ
  have hP := saghar_pt_no_RH hH hrvm hsmall hv ht hu0 hu hΔ hζ hfar
  have hA := titchA_le ht (by linarith : t ≤ T)
  have hA0 := titchA_nonneg ht
  have hN := inner_sum_le hrvm ht htT
  have hN0 : 0 ≤ ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4)
      (by linarith)
    rw [innerZ_eq hfin] at hρ
    exact CH2Section7Z.zetaOrder_nonneg_of_mem
      (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1])
      ((Set.Finite.mem_toFinset hfin).mp hρ)
  have hNZ : (∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ)) / Δ
      ≤ (0.48 * Real.log T + 4.0001) * (8 * (0.52 * Real.log T + 5)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hN hΔi (by positivity) (by linarith)
  have hl := Real.log_le_log ht0 (by linarith : t ≤ T)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hq : 2 / 5 + 1 / (4 * Real.pi) ≤ (1 / 2 : ℝ) := by
    have hp := Real.pi_gt_three
    rw [show (1 / 2 : ℝ) = 2 / 5 + 1 / 10 by norm_num, add_le_add_iff_left,
      div_le_iff₀ (by positivity)]
    linarith
  have hM : (2 / 5 + 1 / (4 * Real.pi)) * Real.log t + 4.001
      ≤ 1 / 2 * Real.log T + 4.001 := by
    have hh := mul_le_mul hq hl hl0 (by norm_num)
    linarith
  have hAu : (1 / 2 + u) * titchA t ≤ 2 * (14.08 * Real.log T + 126) := by
    exact (mul_le_mul_of_nonneg_right (by linarith : 1 / 2 + u ≤ 2) hA0).trans
      (mul_le_mul_of_nonneg_left hA (by norm_num))
  have hit : 1 / t ≤ (1 : ℝ) := by rw [div_le_iff₀ ht0]; linarith
  have hn : 2 * (14.08 * Real.log T + 126) + (1 / 2 * Real.log T + 4.001) +
      (0.48 * Real.log T + 4.0001) * (8 * (0.52 * Real.log T + 5)) + 1
      ≤ 10 * Real.log T ^ 2 := by
    nlinarith [sq_nonneg (Real.log T - 16)]
  linarith

/-- Horizontal integral bound without RH; all real parts of local zeros are allowed. -/
theorem horizontal_integral_no_RH (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {t T L Δ : ℝ} (ht : 1000 ≤ t) (htT : t + 1 / 4 ≤ T)
    (hR : 16 ≤ Real.log T) (hL : 1 ≤ L) (hΔ : 0 < Δ)
    (hΔi : 1 / Δ ≤ 8 * (0.52 * Real.log T + 5))
    (hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im|) :
    ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ *
      Real.exp (-(L * u))
      ≤ 10 * Real.log T ^ 2 / L ^ 2 + Real.exp (-(3 / 2 * (L - 1))) * (15 + 2 * t) := by
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := by linarith
  have i1 := integrableOn_pow_exp 1 hL0
  have j1 := integrableOn_pow_exp 1 one_pos
  have j2 := integrableOn_pow_exp 2 one_pos
  have iK := i1.const_mul (10 * Real.log T ^ 2)
  have iTail := ((j1.const_mul (13 + 2 * t)).add j2).const_mul
    (Real.exp (-(3 / 2 * (L - 1))))
  simp only [Pi.add_apply] at iTail
  have ipt : ∀ u ∈ Ioi (0 : ℝ),
      u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ * Real.exp (-(L * u))
        ≤ (10 * Real.log T ^ 2) * (u ^ 1 * Real.exp (-(L * u))) +
          Real.exp (-(3 / 2 * (L - 1))) *
            ((13 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) +
              u ^ 2 * Real.exp (-(1 * u))) := by
    intro u hu
    have hu0 : 0 < u := hu
    rcases le_or_gt u (3 / 2) with hu1 | hu1
    · have hh := norm_F_le_log_sq hH hrvm hsmall hv ht htT hR hu0.le hu1 hΔ hΔi hfar
      have hs : u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ *
          Real.exp (-(L * u)) ≤ (10 * Real.log T ^ 2) * (u ^ 1 * Real.exp (-(L * u))) := by
        calc _ ≤ u * (10 * Real.log T ^ 2) * Real.exp (-(L * u)) := by gcongr
          _ = _ := by ring
      have hp : 0 ≤ Real.exp (-(3 / 2 * (L - 1))) *
          ((13 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) +
            u ^ 2 * Real.exp (-(1 * u))) := by positivity
      linarith
    · have hζ : riemannZeta (((1 - u : ℝ) : ℂ) + t * I) ≠ 0 := by
        refine CH2ZetaInstance.riemannZeta_ne_zero_of_re_neg (by simp; linarith) fun n hn ↦ ?_
        have hh := congrArg Complex.im hn
        simp at hh
        linarith
      have hF := norm_F_le ht0 hζ
      have hP := adioso_pt hfe hv (t := t) (u := u) (by linarith) hu1.le
      have hit : 1 / t ≤ (1 : ℝ) := by rw [div_le_iff₀ ht0]; linarith
      have he : Real.exp (-(L * u)) ≤
          Real.exp (-(3 / 2 * (L - 1))) * Real.exp (-(1 * u)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hs : u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ *
          Real.exp (-(L * u)) ≤ Real.exp (-(3 / 2 * (L - 1))) *
          ((13 + 2 * t) * (u ^ 1 * Real.exp (-(1 * u))) +
            u ^ 2 * Real.exp (-(1 * u))) := by
        calc _ ≤ u * (13 + 2 * t + u) * Real.exp (-(L * u)) := by gcongr; linarith
          _ ≤ u * (13 + 2 * t + u) *
              (Real.exp (-(3 / 2 * (L - 1))) * Real.exp (-(1 * u))) :=
            mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      have hp : 0 ≤ (10 * Real.log T ^ 2) * (u ^ 1 * Real.exp (-(L * u))) := by positivity
      linarith
  have hm := integral_mono_of_nonneg (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u ↦ u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ *
      Real.exp (-(L * u)))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu ↦ by
      have : (0 : ℝ) < u := hu
      positivity)) (iK.add iTail)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ipt))
  refine hm.trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add iK iTail, integral_const_mul, integral_const_mul,
    integral_add (j1.const_mul _) j2, integral_const_mul,
    integral_pow_exp 1 hL0, integral_pow_exp 1 one_pos, integral_pow_exp 2 one_pos]
  norm_num
  ring

/-- The exponential integral estimate supplies both horizontal integrals in CH2's shift error. -/
theorem horizontal_both_no_RH (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {t T x Δ : ℝ} (ht : 1000 ≤ t) (htT : t + 1 / 4 ≤ T)
    (hR : 16 ≤ Real.log T) (hx : 1 ≤ Real.log x) (hx0 : 0 < x) (hΔ : 0 < Δ)
    (hΔi : 1 / Δ ≤ 8 * (0.52 * Real.log T + 5))
    (hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im|) :
    let J := 10 * Real.log T ^ 2 / Real.log x ^ 2 +
      Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * t)
    (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u)) ≤ x * J ∧
    (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u)) ≤ x * J := by
  dsimp only
  set L := Real.log x with hL
  have hexpL : Real.exp L = x := Real.exp_log hx0
  have hJ := horizontal_integral_no_RH hH hrvm hsmall hv hfe ht htT hR hx hΔ hΔi hfar
  have hrw : ∀ z : ℝ → ℂ, (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (z u)‖ * x ^ (1 - u))
      = x * ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (z u)‖ * Real.exp (-(L * u)) := by
    intro z
    rw [← integral_const_mul]
    congr 1
    funext u
    rw [Real.rpow_def_of_pos hx0, ← hL, show L * (1 - u) = L + -(L * u) by ring, Real.exp_add,
      hexpL]
    ring
  have hplus : ∀ u : ℝ, (1 : ℂ) - u + t * I = ((1 - u : ℝ) : ℂ) + t * I := fun u ↦ by push_cast; ring
  have hminus : ∀ u : ℝ, ‖CH2ZetaInstance.F ((1 : ℂ) - u - t * I)‖
      = ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ := fun u ↦ by
    have e : (1 : ℂ) - u - t * I = (starRingEnd ℂ) (((1 - u : ℝ) : ℂ) + t * I) := by
      apply Complex.ext <;> simp
    rw [e, F_conj, Complex.norm_conj]
  constructor
  · rw [hrw (fun u ↦ (1 : ℂ) - u + t * I)]
    simp only [hplus]
    exact mul_le_mul_of_nonneg_left hJ hx0.le
  · rw [hrw (fun u ↦ (1 : ℂ) - u - t * I)]
    simp only [hminus]
    exact mul_le_mul_of_nonneg_left hJ hx0.le

end CH2QRH
