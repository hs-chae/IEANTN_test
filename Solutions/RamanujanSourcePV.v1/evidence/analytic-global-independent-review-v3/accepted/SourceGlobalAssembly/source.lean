/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.AnalyticMargin
import RamanujanPV.FullFiniteSourcePV

/-! A quantitative source-linked final consumer. Full-count source executions
remain explicit missing inputs. This is NOT an unconditional all-real theorem. -/
namespace RamanujanPV.SourceGlobalAssembly
open Real IEANTN RamanujanPV.AnalyticTransition
set_option autoImplicit false
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

/-- All original scalar source executions plus the SAME24 analytic inputs
imply a uniform actual prime-count gap, conditional on EVERY missing actual
source count execution. No numerical count equality is introduced here. -/
theorem all_real_gap9005_from_completed_counts {rows : List RawFactoredCell}
    (scalars : FullFiniteSourcePV.SourceMarginCertificate 38358837683 1490000000001 9005 rows)
    (counts : ∀r∈rows,QuotientCCell.SourceExecution (r.next-1) r.P ∧
      QuotientCCell.SourceExecution r.j r.Q) :
    ∀x:ℝ,(38358837683:ℝ)≤x→(9005:ℝ)<gap x := by
  intro x hx
  by_cases finite : x<(1490000000001:ℝ)
  · exact FullFiniteSourcePV.gap_from_source_counts scalars counts x hx finite
  · exact AnalyticMargin.analytic_ray_gap9005 hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower (by linarith [le_of_not_gt finite])

end OriginalInputs
#print axioms all_real_gap9005_from_completed_counts
end RamanujanPV.SourceGlobalAssembly
