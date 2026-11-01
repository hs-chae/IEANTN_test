/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTransfer

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Every error term decreases when the selected height is replaced by its lower endpoint. -/
theorem density_remainder_at_height_le {t T x : ℝ} (hT : 2000 ≤ T)
    (ht1 : T - 1 / 2 ≤ t) (ht2 : t ≤ T) (hx : 1000000 ≤ x) :
    Real.pi / t +
      2 * (horizontalCorrection T t x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / t ^ 2 +
      2 * Real.pi / (t * x) *
        ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) +
      Real.pi ^ 2 / (3 * t ^ 2) + Real.log (2 * Real.pi) / x
      ≤ finiteRemainder T x := by
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
  have hpi : Real.pi / t ≤ Real.pi / (T - 1 / 2) := by gcongr
  have hp2 : Real.pi ^ 2 / (3 * t ^ 2) ≤ Real.pi ^ 2 / (3 * (T - 1 / 2) ^ 2) := by
    gcongr
  unfold finiteRemainder
  linarith


/-- Full density-assisted finite CH2 consequence, before certifying the rounded frontier. -/
theorem density_finite_transfer (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    {T x : ℝ} (hT : 3 * (10 : ℝ) ^ (12 : ℕ) + 1 ≤ T) (hR : 16 ≤ Real.log T)
    (hx1 : 1000000 ≤ x) (hxlog : 1 ≤ Real.log x)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T,
      IEANTN.Eψ x ≤ finiteRemainder T x + densitySpectralBound t x := by
  obtain ⟨t, ht, hm⟩ := density_transfer_at_height hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hFKS hRH hT hR hx1 hxlog hqrh
  have ht0 : 0 < t := by norm_num at hT; linarith [ht.1]
  have hx0 : 0 < x := by linarith
  have hp := psi_error_of_main ht0 hx0 hm
  have hrem := density_remainder_at_height_le (by norm_num at hT; linarith : 2000 ≤ T)
    ht.1 ht.2 hx1
  refine ⟨t, ht, ?_⟩
  linarith

end CH2QRH
