/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FiniteTransfer

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Remove CH2's explicit main term using the proved hyperbolic-cotangent bounds. -/
theorem psi_error_of_main {t x R : ℝ} (ht : 0 < t) (hx : 0 < x)
    (h : |Chebyshev.psi x / x -
      (Real.pi / t * (Real.cosh (Real.pi / t) / Real.sinh (Real.pi / t))
        - Real.log (2 * Real.pi) / x)| ≤ R) :
    IEANTN.Eψ x ≤ R + Real.pi ^ 2 / (3 * t ^ 2) + Real.log (2 * Real.pi) / x := by
  have hp := Real.pi_pos
  have hy : 0 < Real.pi / t := by positivity
  have hc := CH2Section7.coth_le_inv_add_div_three hy
  have hc' := mul_le_mul_of_nonneg_left hc hy.le
  have he : Real.pi / t * (1 / (Real.pi / t) + Real.pi / t / 3)
      = 1 + Real.pi ^ 2 / (3 * t ^ 2) := by field_simp
  rw [he] at hc'
  have hs := CH2Section9.sinh_le_mul_cosh hy.le
  have hs0 := Real.sinh_pos_iff.mpr hy
  have hl : 1 ≤ Real.pi / t * (Real.cosh (Real.pi / t) / Real.sinh (Real.pi / t)) := by
    rw [← mul_div_assoc, le_div_iff₀ hs0]
    simpa only [one_mul] using hs
  have hlog : 0 ≤ Real.log (2 * Real.pi) / x := by
    exact div_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three])) hx.le
  have hab : |Real.pi / t * (Real.cosh (Real.pi / t) / Real.sinh (Real.pi / t))
        - Real.log (2 * Real.pi) / x - 1|
      ≤ Real.pi ^ 2 / (3 * t ^ 2) + Real.log (2 * Real.pi) / x := by
    apply abs_le.mpr
    constructor <;> linarith [show 0 ≤ Real.pi ^ 2 / (3 * t ^ 2) by positivity]
  have htri := abs_sub_le (Chebyshev.psi x / x)
    (Real.pi / t * (Real.cosh (Real.pi / t) / Real.sinh (Real.pi / t))
      - Real.log (2 * Real.pi) / x) 1
  have hE : IEANTN.Eψ x = |Chebyshev.psi x / x - 1| := by
    unfold IEANTN.Eψ
    calc |Chebyshev.psi x - x| / x = |(Chebyshev.psi x - x) / x| := by
          rw [abs_div, abs_of_pos hx]
      _ = |Chebyshev.psi x / x - 1| := by rw [sub_div, div_self hx.ne']
  rw [hE]
  linarith

/-- Monotonicity of the explicit zero-count polynomial. -/
theorem spectralBound_mono {t T : ℝ} (ht : 1 ≤ t) (htT : t ≤ T) :
    spectralBound t ≤ spectralBound T := by
  have hp := Real.pi_pos
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hl := Real.log_le_log (by linarith : 0 < t) htT
  have hlT : 0 ≤ Real.log T := hl0.trans hl
  unfold spectralBound
  gcongr

/-- Every error term decreases when the selected height is replaced by its lower endpoint. -/
theorem error_bound_at_height_le {t T x β : ℝ} (hT : 2000 ≤ T)
    (ht1 : T - 1 / 2 ≤ t) (ht2 : t ≤ T) (hx : 1000000 ≤ x) :
    Real.pi / t + spectralBound t * (x ^ β / x) +
      2 * (horizontalCorrection T t x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / t ^ 2 +
      2 * Real.pi / (t * x) *
        ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) +
      Real.pi ^ 2 / (3 * t ^ 2) + Real.log (2 * Real.pi) / x
      ≤ finiteErrorBound T β x := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hU : 0 < T - 1 / 2 := by linarith
  have hp := Real.pi_pos
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hJ : horizontalCorrection T t x ≤ horizontalCorrection T T x := by
    unfold horizontalCorrection
    gcongr
  have hJ0 : 0 ≤ horizontalCorrection T t x := by
    unfold horizontalCorrection
    positivity
  have hK0 : 0 ≤ Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 := by
    have : 0 < Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
    positivity
  have hE : 2 * (horizontalCorrection T t x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / t ^ 2 ≤
      2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / (T - 1 / 2) ^ 2 := by
    apply div_le_div₀ (by linarith) (by linarith [hJ]) (by positivity)
    exact pow_le_pow_left₀ hU.le ht1 2
  have hz : 0 ≤ x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) := by
    have hh : x ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
    positivity
  have he : 2 * Real.pi / (t * x) *
      ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      = (2 * Real.pi / t + 1 / 2) / x * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) := by
    field_simp
    ring
  have htail : 2 * Real.pi / (t * x) *
      ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))))
      ≤ (2 * Real.pi / (T - 1 / 2) + 1 / 2) / x *
        (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) := by
    rw [he]
    gcongr
  have hspec := mul_le_mul_of_nonneg_right (spectralBound_mono (by linarith : 1 ≤ t) ht2)
    (show 0 ≤ x ^ β / x by positivity)
  have hpi : Real.pi / t ≤ Real.pi / (T - 1 / 2) := by gcongr
  have hp2 : Real.pi ^ 2 / (3 * t ^ 2) ≤ Real.pi ^ 2 / (3 * (T - 1 / 2) ^ 2) := by
    gcongr
  unfold finiteErrorBound
  linarith

/-- Fully proved analytic CH2-to-fixed-half-plane transfer, with a free truncation height. -/
theorem finite_transfer (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    {T x β : ℝ} (hT : 2000 ≤ T) (hR : 16 ≤ Real.log T)
    (hx1 : 1000000 ≤ x) (hxlog : 1 ≤ Real.log x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane β) :
    IEANTN.Eψ x ≤ finiteErrorBound T β x := by
  obtain ⟨t, ht, hm⟩ := finite_transfer_at_height hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hT hR hx1 hxlog hqrh
  exact (psi_error_of_main (by linarith [ht.1] : 0 < t) (by linarith : 0 < x) hm).trans
    (error_bound_at_height_le hT ht.1 ht.2 hx1)

end CH2QRH
