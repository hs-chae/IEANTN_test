/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.RawSigma
import PVEvolutionA.SeparatedSpectral
import PVEvolutionA.SlopedRay330
/-! Direct CH2 weighted consumer. The original finite formula is uniform for
0≤σ<1, with a single chosen height. Existing proved limits supplyσ=1.
No Abel-tail allowance, prime-counting reinterpretation or new source premise
is used. The density and finite-RH hypotheses stay explicit. -/
namespace E1FrozenN
open Complex Filter Topology Set MeasureTheory Real WinnerDensityA
open CH2QRH CH2.v7 CH2Section6 CH2Section81 CH2Section9
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Packaging of exactly the thirteen existing namedCH2 source statements. -/
structure DirectCH2Inputs : Prop where
  hfe : ZetaLogDeriv.v1.logDeriv_functional_equation
  hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip
  h24u : CH2.v2.proposition_2_4_upper
  h24l : CH2.v2.proposition_2_4_lower
  hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating
  hneg : ZetaLogDerivValues.v1.logDeriv_neg_one
  h2v : ZetaLogDerivValues.v1.logDeriv_two
  hv : ZetaLogDerivValues.v1.logDeriv_three_halves
  hcs : CotangentSeries.v1.cot_series_zeta_values
  hrvm : ZeroCount.v1.rvm_error_bound
  hsmall : ZeroCount.v1.rvm_error_small
  hlow : LowZeroes.v1.no_zeroes_below_first_ordinate
  hH : ZetaHadamard.v1.logDeriv_partial_fractions

noncomputable def weightedRemainder (T t x : ℝ) : ℝ :=
  Real.pi/t +
    2*(horizontalCorrection T t x+Real.eulerMascheroniConstant/Real.log x^2+
      1.8/Real.log x^3)/t^2+
    2*Real.pi/(t*x)*((1+t/(4*Real.pi))*(x^(-2:ℝ)/(1-x^(-2:ℝ))))

/-- The exact weighted sum after the common-heightσ→1 limit. -/
theorem direct_lambda_at_height (hs : DirectCH2Inputs)
    {T x : ℝ} (hT : 3*(10:ℝ)^(12:ℕ)+1≤T) (hR : 16≤Real.log T)
    (hx1 : 1000000≤x) (hxlog : 1≤Real.log x) :
    ∃t∈Icc (T-1/2) T,
      |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
        rawSpectral t x+weightedRemainder T t x := by
  obtain ⟨t,ht,huniform⟩ := raw_sigma_transfer_at_height hs.hfe hs.hdig hs.h24u hs.h24l
    hs.hk hs.hneg hs.h2v hs.hv hs.hcs hs.hrvm hs.hsmall hs.hlow hs.hH hT hR hx1 hxlog
  have ht0 : 0<t := by linarith [ht.1]
  have hx0 : 0<x := by linarith
  have hlim := ((CH2Section9.tendsto_Svm hx0).sub (CH2Section9.tendsto_main ht0 hx0)).abs
  have hbound : |(∑n∈Finset.Iic ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)/(n:ℝ))-
      (Real.log x-Real.eulerMascheroniConstant)|≤
      Real.pi/t+rawSpectral t x+
        2*(horizontalCorrection T t x+Real.eulerMascheroniConstant/Real.log x^2+
          1.8/Real.log x^3)/t^2+
        2*Real.pi/(t*x)*((1+t/(4*Real.pi))*(x^(-2:ℝ)/(1-x^(-2:ℝ)))) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with σ hσ hσ0
    exact huniform σ hσ0.le hσ
  refine ⟨t,ht,?_⟩
  change |(∑n∈Finset.Iic ⌊x⌋₊,(ArithmeticFunction.vonMangoldt n:ℝ)/(n:ℝ))-
    (Real.log x-Real.eulerMascheroniConstant)|≤_
  unfold weightedRemainder
  linarith only [hbound]

/-- The oldψ finite remainder safely dominates the direct weighted remainder. -/
theorem weightedRemainder_le {t T x : ℝ} (hT : 2000≤T)
    (ht1 : T-1/2≤t) (ht2 : t≤T) (hx : 1000000≤x) :
    weightedRemainder T t x≤finiteRemainder T x := by
  have h := density_remainder_at_height_le hT ht1 ht2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hA : 0≤Real.pi^2/(3*t^2) := by positivity
  have hB : 0≤Real.log (2*Real.pi)/x := div_nonneg hlog hx0.le
  unfold weightedRemainder
  linarith only [h,hA,hB]

/-- Direct weighted finite transfer with exactly the existingCH2 source package. -/
theorem direct_lambda_finite (hs : DirectCH2Inputs)
    {T x : ℝ} (hT : 3*(10:ℝ)^(12:ℕ)+1≤T) (hR : 16≤Real.log T)
    (hx1 : 1000000≤x) (hxlog : 1≤Real.log x) :
    ∃t∈Icc (T-1/2) T,
      |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)|≤
        finiteRemainder T x+rawSpectral t x := by
  obtain ⟨t,ht,h⟩ := direct_lambda_at_height hs hT hR hx1 hxlog
  refine ⟨t,ht,?_⟩
  have hr := weightedRemainder_le (by norm_num at hT;linarith : 2000≤T) ht.1 ht.2 hx1
  linarith only [h,hr]


end E1FrozenN
