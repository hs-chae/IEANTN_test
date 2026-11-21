/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Terence Tao and IEANTN contributors; adapted in this study.
-/
import Section9Limit
import Loose9
open Complex Filter Topology Set MeasureTheory
namespace LooseLimit
open CH2Section6 CH2Section9
set_option maxHeartbeats 1000000 in
/-- **Corollary 1.2, the `ψ` estimate**, at `T ≥ 10⁷ + 1`. The `σ = 0` case of `prop:sagaro`: the
main term's `-ζ'/ζ(0) x^{-1} = -log(2π)/x` is paid for by the `0.0005/√x` that `sagaro_slack`
keeps back. -/
theorem corollary_1_2_psi_at (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper)
    (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (11.1404 : ℝ))
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T) :
    |Chebyshev.psi x - x * CH2.v1.mainFactor T|
      ≤ Real.pi / (T - 1) * x + (CH2.v1.CT T + 0.821) * Real.sqrt x := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hζ0 : riemannZeta ((0 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_zero, riemannZeta_zero]
    norm_num
  have h := Loose9.sagaro_slack hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hplatt hH hT hx9 hxT hRH
    (σ := 0) le_rfl (by norm_num) hζ0
  -- rewrite the `σ = 0` main term
  rw [Svm_zero, Complex.ofReal_zero, logDeriv_zeta_zero] at h
  simp only [Complex.ofReal_re, sub_zero, zero_sub, mul_one] at h
  rw [Real.rpow_one] at h
  have hmf : Real.pi / T * (Real.cosh (Real.pi / T) / Real.sinh (Real.pi / T))
      = CH2.v1.mainFactor T := by
    have hs : Real.sinh (Real.pi / T) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    have hc : Real.cosh (Real.pi / T) ≠ 0 := (Real.cosh_pos _).ne'
    rw [CH2.v1.mainFactor, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hxinv : x ^ (-1 : ℝ) = 1 / x := by
    rw [Real.rpow_neg_one, one_div]
  rw [hmf, hxinv] at h
  -- multiply through by `x`
  have hmul : |x * (Chebyshev.psi x / x
        - (CH2.v1.mainFactor T - Real.log (2 * Real.pi) * (1 / x)))|
      ≤ x * (Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
          - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005 + 0.821) / Real.sqrt x) := by
    rw [abs_mul, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left h hx0.le
  have he : x * (Chebyshev.psi x / x - (CH2.v1.mainFactor T - Real.log (2 * Real.pi) * (1 / x)))
      = Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi) := by
    field_simp
    ring
  have hrhs : x * (Real.pi / (T - 1)
        + (1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
          - 1 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) - 0.0005 + 0.821) / Real.sqrt x)
      = Real.pi / (T - 1) * x + (CH2.v1.CT T + 0.821) * Real.sqrt x - 0.0005 * Real.sqrt x := by
    have hxs : ∀ A : ℝ, x * (A / Real.sqrt x) = A * Real.sqrt x := by
      intro A
      field_simp
      linear_combination (-A) * hss
    rw [CH2.v1.CT, mul_add, hxs]
    ring
  rw [he, hrhs] at hmul
  -- absorb `log 2π`
  have hlog : Real.log (2 * Real.pi) ≤ 0.0005 * Real.sqrt x := by
    have h1 : Real.log (2 * Real.pi) ≤ 1.9 := log_two_pi_le
    have h2 : (31622 : ℝ) ≤ Real.sqrt x := by
      rw [show (31622 : ℝ) = Real.sqrt (31622 ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by nlinarith [show (10 : ℝ) ^ 9 = 1000000000 by norm_num])
    nlinarith
  have hlog0 : |Real.log (2 * Real.pi)| = Real.log (2 * Real.pi) :=
    abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))
  have habs : |Chebyshev.psi x - x * CH2.v1.mainFactor T|
      ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
        + Real.log (2 * Real.pi) := by
    calc |Chebyshev.psi x - x * CH2.v1.mainFactor T|
        = |(Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi))
            + -Real.log (2 * Real.pi)| := by ring_nf
      _ ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
            + |-Real.log (2 * Real.pi)| := abs_add_le _ _
      _ = |Chebyshev.psi x - x * CH2.v1.mainFactor T + Real.log (2 * Real.pi)|
            + Real.log (2 * Real.pi) := by rw [abs_neg, hlog0]
  linarith


end LooseLimit
