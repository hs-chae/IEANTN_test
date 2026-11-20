/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticMargin
import RamanujanPV.CoupledAnalyticStrip

/-! Additional analytic conclusion; original source arrays/results unchanged.
The exact original 24 inputs are preserved and the ONE additional source input
is explicitly Büthe2017 final Theorem2(1.6). No finite numerical computation,
prime-count equality, endpoint positivity or pi144 expansion is assumed. -/
namespace RamanujanPV.CoupledFinalAnalytic
open Real Set RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0

section OriginalInputs
variable
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hFKS : FKS.v3.density_0618) (hRH : PlattTrudgian.v1.rh_up_to)
    (hseries : LogIntegralSeriesIdentity IEANTN.li)
    (hoffset : Middle.LiOffsetIdentity)
    (hpositive : ButhePiBelowLi)
    (hbuthe : ButhePiLower IEANTN.primeCounting IEANTN.li)
    (hCH2 : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤
      Real.pi / (3 * (10 : ℝ)^12) * t + (113.67 : ℝ) * sqrt t)
    (hDusart : Middle.DusartPowerInput)

include hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hqrh hFKS hRH
  hseries hoffset hpositive hbuthe hCH2 hDusart

variable (htheta : ButheThetaDeficit) (hlower : AxlerPiLower)
include htheta hlower

variable (hupper : CoupledActualPi.ButheThetaUpper)
include hupper

/-- Whole actual-prime-count ray, retaining the earlier uniform9005 gap.
The lower transition comes from the newly proved correlated-error strip;
the original ray is applied on its original domain. -/
theorem analytic_ray_gap9005_from1250 {x : ℝ} (hx : (1250000000000:ℝ) ≤ x) :
    (9005:ℝ) < gap x := by
  by_cases h1490 : (1490000000000:ℝ) ≤ x
  · exact AnalyticMargin.analytic_ray_gap9005 hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower h1490
  · exact CoupledAnalyticStrip.gap9005 hseries hoffset hpositive hbuthe htheta hlower
      hupper ⟨hx,le_of_not_ge h1490⟩

/-- Ramanujan's strict inequality for every realx at and beyond1.25T.
This theorem has25named analytic/source inputs, not the old24-input signature. -/
theorem analytic_ray_from1250 {x : ℝ} (hx : (1250000000000:ℝ) ≤ x) : Holds x := by
  apply (holds_iff_gap_pos x).2
  exact (by norm_num : (0:ℝ)<9005).trans
    (analytic_ray_gap9005_from1250 hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower hupper hx)
end OriginalInputs

#print axioms analytic_ray_gap9005_from1250
#print axioms analytic_ray_from1250
end RamanujanPV.CoupledFinalAnalytic
