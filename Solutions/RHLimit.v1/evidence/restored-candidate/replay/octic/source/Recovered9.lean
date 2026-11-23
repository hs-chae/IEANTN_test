/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Terence Tao and IEANTN contributors; adapted in this study.
-/
import Section9
import Recovered7
open Complex Filter Topology Set MeasureTheory
namespace Recovered9
open CH2Section6 CH2Section81 CH2Section9
set_option maxHeartbeats 1000000 in
/-- **`prop:sagaro` at the height chosen by `lem:hardin`.** -/
theorem sagaro_at_t (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper)
    (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (10.5 : ℝ))
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        ≤ Real.pi / t
          + (1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
              - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi)) + 0.181) / Real.sqrt x
          + 2 * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
              + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x
              + Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) / t ^ 2
          + 2 * Real.pi / (t * x)
              * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hx1 : (1000000 : ℝ) ≤ x := by linarith [show (1000000 : ℝ) ≤ 10 ^ 9 by norm_num]
  obtain ⟨t, ⟨ht1, ht2⟩, hTfree, hInt1, hInt2⟩ := hardin hH hrvm hsmall hv hfe (by linarith) hx9 hxT hRH
  have ht7 : (10 : ℝ) ^ 7 - 1 ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have ht4 : (4 : ℝ) ≤ t := by linarith [show (4 : ℝ) ≤ 10 ^ 7 by norm_num]
  have hRHt : IEANTN.RiemannHypothesisUpTo t := RH_mono ht2 hRH
  obtain ⟨l, hsig, hlT, hlδ⟩ := exists_ladder (by linarith : (4 : ℝ) < t)
  have hRC := CH2Section6.hRC_of_rvm hsmall l hlδ
  have hTfree' : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T := by rw [hlT]; exact hTfree
  have hlam : CH2Section6.lamOf l.T σ < 0 := CH2Section6.lamOf_neg l.hT hσ1
  have hsig0 : 0 ≤ l.sigmaOf (CH2Section6.lamOf l.T σ) := by
    rw [CH2Section6.sigmaOf_lamOf l hσ1]; exact hσ0
  -- `Z`: the zero sum, from `prop:vihuela`
  set V : ℝ := 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
    - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi)) + 0.181 with hV
  have hZ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      IEANTN.zetaZeroesSum (Set.Iic 1) (Set.Ioc l.δ l.T)
          (fun ρ ↦ ‖CH2Section6.omegaPlus l.T σ ρ + ε * I * CH2Section6.thetaTS l.T 1 ρ‖
            * x ^ ρ.re) ≤ Real.sqrt x * (V * (t / (2 * Real.pi))) := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    rw [hlδ, hlT, zsum_Iic_Ioc_eq hsmall, zsum_weight_sqrt ht0.le hx0 hRHt]
    have hvi := Recovered7.vihuela hcs hrvm hsmall hplatt (T := t) (σ := σ) (ξ := ε) ht7 hRHt
      (fun z hz ↦ fun h ↦ hTfree z hz (by rw [h]; exact abs_of_pos ht0)) hσ0 hσ1 hε1
    rw [← hV] at hvi
    have hS : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)
        ≤ V * (t / (2 * Real.pi)) := by
      rw [← sub_nonneg] at hvi
      rw [← sub_nonneg]
      have e : V * (t / (2 * Real.pi))
          - IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
            (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)
          = (t / (2 * Real.pi)) * (V - 2 * Real.pi / t * IEANTN.zetaZeroesSum Set.univ
            (Set.Ioc 0 t) (fun ρ ↦ ‖CH2Section6.omegaPlus t σ ρ
              + (ε : ℂ) * I * CH2Section6.thetaTS t 1 ρ‖)) := by
        field_simp
      rw [e]
      exact mul_nonneg (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg x)
  -- `E`: the shift error, from `lem:hardin` and `norm_intC_le`
  set J : ℝ := 12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
    + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x with hJ
  set K : ℝ := Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 with hK
  have hE : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      CH2Section6.shiftError l (CH2Section6.lamOf l.T σ) ε x ≤ x / (Real.pi * t) * (J + K) := by
    intro ε hε
    have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    have hC := CH2Section6.norm_intC_le hfe hdig hk hneg h2v l hlδ hlam hε1 (by rw [hlT]; exact ht4)
      hsig0 hRC hx1
    rw [hlT] at hC ⊢
    rw [CH2Section6.shiftError, hlT]
    have hKx : (Real.eulerMascheroniConstant * x / Real.log x ^ 2 + 1.8 * x / Real.log x ^ 3) / t
        = x * K / t := by rw [hK]; field_simp; try ring
    rw [hKx] at hC
    have e : x / (Real.pi * t) * (J + K)
        = 1 / (2 * Real.pi) * (1 / t * (x * J + x * J) + 2 * (x * K / t)) := by
      field_simp
      try ring
    rw [e]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hI1 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
        ≤ x * J := hInt1
    have hI2 : (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ x * J := by
      refine le_trans (le_of_eq ?_) hInt2
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      congr 2
      try push_cast
      try ring
    have hle : 1 / t * ((∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
          + ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
        ≤ 1 / t * (x * J + x * J) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- apply `svm_abs_bound`
  have hmain := CH2Section6.svm_abs_bound hfe hdig h24u h24l hsig hTfree' hRC hσ0 hσ1 hσζ
    (x₀ := 2) (by norm_num) (by linarith [show (2 : ℝ) < 10 ^ 9 by norm_num]) hZ hE
  rw [hlT] at hmain
  refine ⟨t, ⟨ht1, ht2⟩, hmain.trans (le_of_eq ?_)⟩
  set r : ℝ := Real.sqrt x with hr
  have hx' : x = r * r := (Real.mul_self_sqrt hx0.le).symm
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hx0
  have e1 : 2 * Real.pi / (t * x) * (r * (V * (t / (2 * Real.pi)))) = V / r := by
    rw [hx']
    field_simp
    try ring
  have e2 : 2 * Real.pi / (t * x) * (x / (Real.pi * t) * (J + K)) = 2 * (J + K) / t ^ 2 := by
    field_simp
    try ring
  have e3 : 2 * Real.pi / (t * x)
      * (r * (V * (t / (2 * Real.pi)))
        + (1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))
        + x / (Real.pi * t) * (J + K))
      = 2 * Real.pi / (t * x) * (r * (V * (t / (2 * Real.pi))))
        + 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
        + 2 * Real.pi / (t * x) * (x / (Real.pi * t) * (J + K)) := by ring
  rw [e3, e1, e2, hV, hJ, hK]
  ring

/-! ### `lem:cothder` and the passage from `t` to `T` -/

/-- `sinh w ≤ w cosh w` for `w ≥ 0`: the derivative of `w cosh w - sinh w` is `w sinh w ≥ 0`. -/
theorem sinh_le_mul_cosh {w : ℝ} (hw : 0 ≤ w) : Real.sinh w ≤ w * Real.cosh w := by
  have hd : ∀ v : ℝ, HasDerivAt (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) (v * Real.sinh v) v := by
    intro v
    have h1 : HasDerivAt (fun u : ℝ ↦ u * Real.cosh u) (1 * Real.cosh v + v * Real.sinh v) v :=
      (hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)
    exact (h1.sub (Real.hasDerivAt_sinh v)).congr_deriv (by ring)
  have hnn : ∀ v : ℝ, 0 ≤ v * Real.sinh v := by
    intro v
    rcases le_total 0 v with h | h
    · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
    · nlinarith [Real.sinh_nonpos_iff.mpr h]
  have hmono : Monotone (fun u : ℝ ↦ u * Real.cosh u - Real.sinh u) :=
    monotone_of_deriv_nonneg (fun v ↦ (hd v).differentiableAt)
      (fun v ↦ by rw [(hd v).deriv]; exact hnn v)
  have h0 := hmono hw
  simp only [zero_mul, Real.sinh_zero, sub_zero, sub_self] at h0
  linarith

set_option maxHeartbeats 1000000 in
/-- **`prop:sagaro` with the main term at `T`.** `sagaro_at_t` plus `coth_main_shift`; the error
is still expressed in terms of the chosen `t`. -/
theorem sagaro_shifted (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper)
    (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (10.5 : ℝ))
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        ≤ Real.pi / t
          + (1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) ^ 2
              - 1.001 / (6 * Real.pi) * Real.log (t / (2 * Real.pi)) + 0.181) / Real.sqrt x
          + 2 * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
              + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x
              + Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) / t ^ 2
          + 2 * Real.pi / (t * x)
              * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
          + Real.pi ^ 2 / (2 * t ^ 2 * T) := by
  have hπ := Real.pi_pos
  obtain ⟨t, ⟨ht1, ht2⟩, hbd⟩ := sagaro_at_t hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hplatt hH
    hT hx9 hxT hRH hσ0 hσ1 hσζ
  have ht0 : (0 : ℝ) < t := by
    have : (0 : ℝ) < 10 ^ 7 := by norm_num
    linarith
  refine ⟨t, ⟨ht1, ht2⟩, ?_⟩
  have hshift := coth_main_shift (σ := σ) (t := t) (T := T) hσ1 ht0 ht2
  have hnum : Real.pi * (Real.pi * (1 - σ)) * (1 / t - 1 / T) / t ≤ Real.pi ^ 2 / (2 * t ^ 2 * T) := by
    have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
    have h1 : 1 / t - 1 / T = (T - t) / (t * T) := by field_simp
    rw [h1]
    have h2 : (T - t) / (t * T) ≤ (1 / 2) / (t * T) := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : Real.pi * (Real.pi * (1 - σ)) ≤ Real.pi ^ 2 := by nlinarith
    have h4 : (0 : ℝ) ≤ (T - t) / (t * T) := by
      apply div_nonneg (by linarith) (by positivity)
    calc Real.pi * (Real.pi * (1 - σ)) * ((T - t) / (t * T)) / t
        ≤ Real.pi ^ 2 * ((T - t) / (t * T)) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le
          exact mul_le_mul_of_nonneg_right h3 h4
      _ ≤ Real.pi ^ 2 * ((1 / 2) / (t * T)) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.pi ^ 2 / (2 * t ^ 2 * T) := by field_simp; try ring
  have htri : |CH2Section6.Svm σ x / x ^ (1 - σ)
      - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
        - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ |CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
        + |Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - Real.pi / T
              * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))| := by
    have := abs_add_le (CH2Section6.Svm σ x / x ^ (1 - σ)
      - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
        - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1)))
      (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
        - Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T)
          / Real.sinh (Real.pi * (1 - σ) / T)))
    calc _ = |(CH2Section6.Svm σ x / x ^ (1 - σ)
          - (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t) / Real.sinh (Real.pi * (1 - σ) / t))
            - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1)))
          + (Real.pi / t * (Real.cosh (Real.pi * (1 - σ) / t)
              / Real.sinh (Real.pi * (1 - σ) / t))
            - Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T)
              / Real.sinh (Real.pi * (1 - σ) / T)))| := by ring_nf
      _ ≤ _ := this
  linarith

/-! ### The numeric collapse: from the height `t` to `T` -/

theorem log_two_pi_le : Real.log (2 * Real.pi) ≤ 1.9 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  rw [Real.log_le_iff_le_exp (by positivity), show (1.9 : ℝ) = (1 : ℕ) + 0.9 by norm_num,
    Real.exp_add]
  have h1 := (CH2Section7A.exp_nat_bounds 1).1
  have hs := CH2Section7A.exp_small_ge (x := 0.9) (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.exp 0.9 := (Real.exp_pos _).le
  calc 2 * Real.pi ≤ 2 * 3.15 := by linarith
    _ ≤ (2.7182818283 : ℝ) ^ 1 * (1 + 0.9 + 0.9 ^ 2 / 2 + 0.9 ^ 3 / 6 + 0.9 ^ 4 / 24) := by
        norm_num
    _ ≤ (2.7182818283 : ℝ) ^ 1 * Real.exp 0.9 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ Real.exp ((1 : ℕ) : ℝ) * Real.exp 0.9 := mul_le_mul_of_nonneg_right h1 h0

/-- `log T ≤ 2√T`, hence `(log T + 10)² ≤ 9T` once `T ≥ 64`. -/
theorem log_add_ten_sq_le {T : ℝ} (hT : 64 ≤ T) : (Real.log T + 10) ^ 2 ≤ 9 * T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h8 : (8 : ℝ) ≤ Real.sqrt T := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hT
  have hlog : Real.log T ≤ 2 * Real.sqrt T - 2 := by
    have h1 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hT0.le
    rw [h2] at h1
    linarith
  have hR0 : 0 ≤ Real.log T + 10 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ T by linarith)
    linarith
  have hR3 : Real.log T + 10 ≤ 3 * Real.sqrt T := by linarith
  calc (Real.log T + 10) ^ 2 ≤ (3 * Real.sqrt T) ^ 2 := by
        exact pow_le_pow_left₀ hR0 hR3 2
    _ = 9 * T := by rw [mul_pow, Real.sq_sqrt hT0.le]; ring

set_option maxHeartbeats 4000000 in
/-- **`prop:sagaro`, with the leftover margin kept.** The error terms of `sagaro_shifted` collapse
into `π/(T-1)` and the `prop:vihuela` block; the `1.001` in the latter pays for everything else on
the `1/√x` side and still leaves `0.0005/√x`, which `Corollary 1.2` needs at `σ = 0` to absorb
`ζ'/ζ(0) = log 2π`. -/
theorem sagaro_slack (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper)
    (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (10.5 : ℝ))
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x σ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0) :
    |CH2Section6.Svm σ x / x ^ (1 - σ)
        - (Real.pi / T * (Real.cosh (Real.pi * (1 - σ) / T) / Real.sinh (Real.pi * (1 - σ) / T))
          - (deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re * x ^ (σ - 1))|
      ≤ Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
            - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005 + 0.181) / Real.sqrt x := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  obtain ⟨t, ⟨ht1, ht2⟩, hbd⟩ := sagaro_shifted hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hplatt hH
    hT hx9 hxT hRH hσ0 hσ1 hσζ
  have h107 : (10000000 : ℝ) = (10 : ℝ) ^ 7 := by norm_num
  have h109 : (1000000000 : ℝ) = (10 : ℝ) ^ 9 := by norm_num
  have hT0 : (10000000 : ℝ) ≤ T := by rw [h107] at *; linarith
  have hx0 : (1000000000 : ℝ) ≤ x := by rw [h109]; exact hx9
  have hxpos : (0 : ℝ) < x := by linarith
  have ht0 : (9999999 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  refine hbd.trans ?_
  -- names
  set R : ℝ := Real.log T with hRdef
  set L : ℝ := Real.log x with hLdef
  set y : ℝ := Real.log (T / (2 * Real.pi)) with hydef
  set z : ℝ := Real.log (t / (2 * Real.pi)) with hzdef
  set s : ℝ := Real.sqrt x with hsdef
  have hs0 : (0 : ℝ) < s := Real.sqrt_pos.mpr hxpos
  -- the logarithms
  have hR16 : 16.1 ≤ R := by
    have h1 : Real.log ((10 : ℝ) ^ 7) ≤ R := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hL20 : 20.7 ≤ L := by
    have h1 : Real.log ((10 : ℝ) ^ 9) ≤ L := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hRL : R ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  have hzy : z ≤ y := Real.log_le_log (by positivity) (by gcongr)
  have hz135 : 13.5 ≤ z := by
    have hzeq : z = Real.log t - Real.log (2 * Real.pi) := by
      rw [hzdef, Real.log_div (by linarith) (by positivity)]
    have hlt : Real.log ((10 : ℝ) ^ 7 / 2) ≤ Real.log t :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow] at hlt
    push_cast at hlt
    linarith [log_ten_ge, log_two_pi_le, Real.log_two_lt_d9]
  have hy135 : 13.5 ≤ y := by linarith
  -- the `1/√x` block
  have hslack : 4 * (R + 10) ^ 2 / t ^ 2 + 0.0005 ≤ 0.001 / (6 * Real.pi) * z := by
    have h1 : (R + 10) ^ 2 ≤ 9 * T := log_add_ten_sq_le (by linarith)
    have h2 : T ^ 2 / 2 ≤ t ^ 2 := by nlinarith
    have h3 : 4 * (R + 10) ^ 2 / t ^ 2 ≤ 72 / T := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have h4 : (72 : ℝ) / T ≤ 0.0000072 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h5 : 0.001 / (6 * Real.pi) * z ≥ 0.001 / (6 * Real.pi) * 13.5 := by
      apply mul_le_mul_of_nonneg_left hz135 (by positivity)
    have h6 : (0.0007 : ℝ) ≤ 0.001 / (6 * Real.pi) * 13.5 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hkey2 : (1 / (2 * Real.pi) * z ^ 2 - 1.001 / (6 * Real.pi) * z) / s
        + 4 * (R + 10) ^ 2 / t ^ 2 / s
      ≤ (1 / (2 * Real.pi) * y ^ 2 - 1 / (6 * Real.pi) * y - 0.0005) / s := by
    rw [← add_div, div_le_div_iff_of_pos_right hs0]
    have hbracket : 0 ≤ 1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) - 1 / (6 * Real.pi) * (y - z) := by
      have h1 : 1 / (6 * Real.pi) * (y - z) ≤ 1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) := by
        have hyz : 0 ≤ y - z := by linarith
        have h2 : y ^ 2 - z ^ 2 = (y - z) * (y + z) := by ring
        rw [h2]
        have h3 : 1 / (6 * Real.pi) ≤ 1 / (2 * Real.pi) * (y + z) := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) / (2 * Real.pi) * (y + z) * (6 * Real.pi) = 3 * (y + z) := by
            field_simp; ring
          rw [this]
          linarith
        nlinarith
      linarith
    have he : 1 / (2 * Real.pi) * y ^ 2 - 1 / (6 * Real.pi) * y
        - (1 / (2 * Real.pi) * z ^ 2 - 1.001 / (6 * Real.pi) * z)
        = (1 / (2 * Real.pi) * (y ^ 2 - z ^ 2) - 1 / (6 * Real.pi) * (y - z))
          + 0.001 / (6 * Real.pi) * z := by ring
    linarith
  -- the `π/T` block
  have htriv : 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      ≤ 0.001 / t ^ 2 := by
    have hx2 : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
      rw [Real.rpow_neg hxpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
    rw [hx2]
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx2ne : x ^ 2 - 1 ≠ 0 := by nlinarith
    have hne : 1 - 1 / x ^ 2 ≠ 0 := by
      have h9 : 1 / x ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
      intro hc
      rw [sub_eq_zero] at hc
      linarith [hc.symm.le]
    have hd : 1 / x ^ 2 / (1 - 1 / x ^ 2) = 1 / (x ^ 2 - 1) := by
      field_simp
      try ring
    rw [hd]
    have h1 : 1 / (x ^ 2 - 1) ≤ 2 / x ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    have h2 : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) ≤ 0.51 / x := by
      have e : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi))
          = 2 * Real.pi / (t * x) + 1 / (2 * x) := by field_simp; ring
      rw [e]
      have h3 : 2 * Real.pi / (t * x) ≤ 0.01 / x := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have h4 : 1 / (2 * x) = 0.5 / x := by field_simp; ring
      rw [h4] at *
      have : (0.01 : ℝ) / x + 0.5 / x = 0.51 / x := by field_simp; ring
      linarith
    have h5 : 0 ≤ 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) := by positivity
    have h6 : 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1)))
        = 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1)) := by ring
    rw [h6]
    have h7 : 2 * Real.pi / (t * x) * (1 + t / (4 * Real.pi)) * (1 / (x ^ 2 - 1))
        ≤ 0.51 / x * (2 / x ^ 2) := by
      exact mul_le_mul h2 h1 (div_nonneg (by norm_num) (by nlinarith)) (by positivity)
    have h8 : (0.51 : ℝ) / x * (2 / x ^ 2) ≤ 0.001 / t ^ 2 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have htx : t ≤ x := by linarith
      have h9 : t ^ 2 ≤ x ^ 2 := by nlinarith
      nlinarith [h9, mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ x - 1020)]
    linarith
  have hcoth : Real.pi ^ 2 / (2 * t ^ 2 * T) ≤ 0.000001 / t ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.pi ^ 2 ≤ 0.000002 * T := by nlinarith
    calc Real.pi ^ 2 * t ^ 2 ≤ (0.000002 * T) * t ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
      _ = 0.000001 * (2 * t ^ 2 * T) := by ring
  have hI : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) ≤ 1.51 := by
    have hγ := Real.eulerMascheroniConstant_lt_two_thirds
    have hL2 : (20.7 : ℝ) * L ≤ L ^ 2 := by nlinarith
    have hL3 : (20.7 : ℝ) ^ 2 * L ≤ L ^ 3 := by nlinarith
    have h1 : 12.5 * R / L ^ 2 ≤ 0.605 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : 62 * R / L ^ 3 ≤ 0.145 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h3 : Real.eulerMascheroniConstant / L ^ 2 ≤ 0.0016 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h4 : (1.8 : ℝ) / L ^ 3 ≤ 0.0003 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hkey1 : Real.pi / t
      + 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
          + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
      + 2 * Real.pi / (t * x) * ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      + Real.pi ^ 2 / (2 * t ^ 2 * T)
      ≤ Real.pi / (T - 1) := by
    have hIt : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2 ≤ 1.51 / t ^ 2 := by
      apply div_le_div_of_nonneg_right hI (by positivity)
    have hsum : 1.51 / t ^ 2 + 0.001 / t ^ 2 + 0.000001 / t ^ 2 ≤ Real.pi / 2 / t ^ 2 := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have hq1 : (0 : ℝ) < (T - 1) * (T - 1 / 2) := mul_pos (by linarith) (by linarith)
    have hq2 : (T - 1) * (T - 1 / 2) ≤ t ^ 2 := by nlinarith [ht1, hT0]
    have hle : Real.pi / 2 / t ^ 2 ≤ Real.pi / 2 / ((T - 1) * (T - 1 / 2)) :=
      div_le_div_of_nonneg_left (by positivity) hq1 hq2
    have hpt : Real.pi / t ≤ Real.pi / (T - 1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) ht1
    have hsplit : Real.pi / (T - 1 / 2) + Real.pi / 2 / ((T - 1) * (T - 1 / 2))
        = Real.pi / (T - 1) := by
      have hT1 : (T : ℝ) - 1 ≠ 0 := by intro h; linarith
      have hT2 : (T : ℝ) - 1 / 2 ≠ 0 := by intro h; linarith
      rw [div_add_div _ _ hT2 (ne_of_gt hq1),
        div_eq_div_iff (mul_ne_zero hT2 (ne_of_gt hq1)) hT1]
      ring
    linarith
  -- combine
  have hJsplit : 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3 + 2 * (R + 10) ^ 2 / s
        + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
      = 2 * (12.5 * R / L ^ 2 + 62 * R / L ^ 3
          + Real.eulerMascheroniConstant / L ^ 2 + 1.8 / L ^ 3) / t ^ 2
        + 4 * (R + 10) ^ 2 / t ^ 2 / s := by
    field_simp
    ring
  rw [hJsplit]
  simp only [add_div] at hkey1 hkey2 ⊢
  linarith


end Recovered9
