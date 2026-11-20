/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CoupledFinalAnalytic
import RamanujanPV.AnalyticGlue

/-! The unchanged study-level certificate interface with the shorter analytic
transition. This is a conditional assembly: no full finite witness is claimed.
The 25 analytic/source hypotheses remain explicit; the missing finite input
retains actual counts, real enclosures, strict inequalities and exact coverage. -/
namespace RamanujanPV.CoupledGlobalAssembly
open Real Set RamanujanPV.AnalyticTransition
set_option autoImplicit false

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

theorem all_real_from_completed_finite_certificate {cells : List Cell}
    (certificate : CompleteCertificate 38358837683 1250000000001 cells) :
    ∀ x : ℝ, (38358837683:ℝ) ≤ x → Holds x := by
  intro x hx
  by_cases hfinite : x < (1250000000001:ℝ)
  · exact complete_certificate_sound certificate x (by exact_mod_cast hx) hfinite
  · exact CoupledFinalAnalytic.analytic_ray_from1250 hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower hupper (by linarith [le_of_not_gt hfinite])
end OriginalInputs

#print axioms all_real_from_completed_finite_certificate
end RamanujanPV.CoupledGlobalAssembly
