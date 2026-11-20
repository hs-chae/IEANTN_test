/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullAdaptiveSourcePV.Final
import RamanujanPV.SourceGlobalAssembly

/-! Concrete every-row source-scalar result and a final quantitative consumer.
The full prime-count execution witness is explicitly OPEN, not manufactured by
this wrapper. No original mathematical input or numerical row is changed. -/
namespace RamanujanPV.FullSourceResult
open Real IEANTN RamanujanPV.AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Exact C bytes for the SAME ASTs executed by the full scalar/count model. -/
def ActualProgramBindings : Prop :=
  LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSource.render QuotientCSource.actualSource () ∧
  LCMSourcePV.RestrictedC.SourceCorresponds FiniteExpSource.render FiniteExpSource.actualSource () ∧
  LCMSourcePV.RestrictedC.SourceCorresponds FiniteLogSource.render FiniteLogSource.actualSource () ∧
  LCMSourcePV.RestrictedC.SourceCorresponds FiniteCellSource.render FiniteCellSource.actualSource ()

theorem actual_program_bindings : ActualProgramBindings :=
  ⟨QuotientCSource.actual_source_checked,FiniteExpSource.actual_source_checked,
    FiniteLogSource.actual_source_checked,FiniteCellSource.actual_source_checked⟩

/-- Unconditional actual e/log/cell source executions and retained arithmetic
margin for ALL1755663 original rows; intentionally NO count-truth conclusion. -/
theorem all_scalar_programs : ActualProgramBindings ∧
    FullFiniteSourcePV.SourceMarginCertificate 38358837683 1490000000001 9005
      FullAdaptiveSourcePV.allRows :=
  ⟨actual_program_bindings,FullAdaptiveSourcePV.all_source_margins⟩

/-- The mathematical obligation not discharged by the scalar program study. -/
def RemainingCountExecutions : Prop :=
  ∀r∈FullAdaptiveSourcePV.allRows,QuotientCCell.SourceExecution (r.next-1) r.P ∧
    QuotientCCell.SourceExecution r.j r.Q

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

/-- Exact concrete final consumer. Every full-prefix actual source-count run
remains a required argument, in addition to the SAME24 analytic hypotheses. -/
theorem all_real_gap9005_if_counts_completed (counts : RemainingCountExecutions) :
    ActualProgramBindings ∧∀x:ℝ,(38358837683:ℝ)≤x→(9005:ℝ)<gap x :=
  ⟨actual_program_bindings,
    SourceGlobalAssembly.all_real_gap9005_from_completed_counts hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
      htheta hlower FullAdaptiveSourcePV.all_source_margins counts⟩

end OriginalInputs
#print axioms actual_program_bindings
#print axioms all_scalar_programs
#print axioms all_real_gap9005_if_counts_completed
end RamanujanPV.FullSourceResult
