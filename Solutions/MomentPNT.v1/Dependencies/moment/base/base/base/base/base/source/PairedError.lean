/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedTransfer
import PsiError

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

noncomputable def pairedErrorBound (T β x : ℝ) : ℝ :=
  (finiteErrorBound T β x + finiteErrorBound T (1 - β) x) / 2

/-- Remove the selected height in the paired formula, preserving the shared remainder. -/
theorem paired_error_at_height_le {t T x β : ℝ} (hT : 2000 ≤ T)
    (ht1 : T - 1 / 2 ≤ t) (ht2 : t ≤ T) (hx : 1000000 ≤ x) :
    Real.pi / t + spectralBound t * ((x ^ β + x ^ (1 - β)) / (2 * x)) +
      2 * (horizontalCorrection T t x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / t ^ 2 +
      2 * Real.pi / (t * x) *
        ((1 + t / (4 * Real.pi)) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) +
      Real.pi ^ 2 / (3 * t ^ 2) + Real.log (2 * Real.pi) / x ≤ pairedErrorBound T β x := by
  have h1 := error_bound_at_height_le (β := β) hT ht1 ht2 hx
  have h2 := error_bound_at_height_le (β := 1 - β) hT ht1 ht2 hx
  unfold pairedErrorBound
  have he : spectralBound t * ((x ^ β + x ^ (1 - β)) / (2 * x)) =
      (spectralBound t * (x ^ β / x) + spectralBound t * (x ^ (1 - β) / x)) / 2 := by ring
  rw [he]
  linarith

/-- Fully proved analytic CH2-to-fixed-half-plane transfer, with a free truncation height. -/
theorem paired_finite_transfer (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    IEANTN.Eψ x ≤ pairedErrorBound T β x := by
  obtain ⟨t, ht, hm⟩ := paired_transfer_at_height hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hT hR hx1 hxlog hqrh
  exact (psi_error_of_main (by linarith [ht.1] : 0 < t) (by linarith : 0 < x) hm).trans
    (paired_error_at_height_le hT ht.1 ht.2 hx1)

end CH2QRH
