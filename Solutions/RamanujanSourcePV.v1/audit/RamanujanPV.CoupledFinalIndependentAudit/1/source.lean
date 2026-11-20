/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CoupledFinalAnalytic
import Lean.Util.FoldConsts

/-! Independent exact 25-input types and complete proof/type closure census.
This is a bounded audit of the actual coupled strip/ray, not a source census
of IEANTN or a source-first numerical-program verification claim. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let common : List Name := [
    `IEANTN.primeCounting, `Nat.primeCounting, `IEANTN.li, `Chebyshev.theta,
    `RamanujanPV.gap,
    `RamanujanPV.CoupledActualPi.ButheThetaUpper,
    `RamanujanPV.CoupledActualPi.actual_coupled_envelope,
    `RamanujanPV.CoupledActualPi.actual_pi_identity,
    `RamanujanPV.CoupledActualPi.initialConstant,
    `RamanujanPV.CoupledActualPi.sharedIntegral,
    `RamanujanPV.CoupledActualPi.shared_split,
    `RamanujanPV.CoupledActualPi.shared_anchor,
    `RamanujanPV.CoupledActualPi.shared_upper,
    `RamanujanPV.CoupledActualPi.counts_with_shared_integral,
    `RamanujanPV.ActualPartialSummation.piMinusLi_eq,
    `RamanujanPV.CoupledIntegralEnvelope.at_upper_from_counts,
    `RamanujanPV.CoupledIntegralEnvelope.antitone_from_lower,
    `RamanujanPV.CoupledIntegralBounds.integral_upper,
    `RamanujanPV.CoupledScalarComparison.comparison,
    `RamanujanPV.CoupledUniformBounds.Uerr_uniform,
    `RamanujanPV.CoupledStripGuards.antitone_guard,
    `RamanujanPV.CoupledStripGuards.li_lower_guard,
    `RamanujanPV.CoupledBaseEnvelope.R_hasDerivAt,
    `RamanujanPV.CoupledBaseEnvelope.monotone_strip,
    `RamanujanPV.CoupledBaseEnvelope.endpoint_positive,
    `RamanujanPV.CoupledBaseEnvelope.series1250_lower,
    `RamanujanPV.CoupledBaseEnvelope.series1250_upper,
    `RamanujanPV.CoupledBaseEnvelope.series1250e_lower,
    `RamanujanPV.CoupledBaseEnvelope.series1250e_upper,
    `RamanujanPV.CoupledBaseEnvelope.log_mantissa1250,
    `RamanujanPV.CoupledBaseEnvelope.strip_positive,
    `RamanujanPV.CoupledAnalyticStrip.normalized_margin]
  let whole : List Name := [
    `RamanujanPV.CoupledAnalyticStrip.gap9005,
    `RamanujanPV.AnalyticMargin.analytic_ray_gap9005,
    `RamanujanPV.FinalAnalytic.quantitative_from40,
    `RamanujanPV.QRHFullTail.pi_two_sided_144]
  let forbiddenPrefixes := ["RamanujanPV.HighTransitionCount.",
    "RamanujanPV.DemandCriticalPair.", "RamanujanPV.LocalWindowMillion.",
    "RamanujanPV.LocalCellsMillion.", "RamanujanPV.FiniteGuardedMillion.",
    "RamanujanPV.FiniteGuardedResult.", "RamanujanPV.FullAdaptiveSourcePV.",
    "RamanujanPV.FullSourceResult.", "RamanujanPV.SourceGlobalAssembly."]
  for (root,required) in [
      (`RamanujanPV.CoupledAnalyticStrip.gap9005,common),
      (`RamanujanPV.CoupledFinalAnalytic.analytic_ray_gap9005_from1250,common++whole),
      (`RamanujanPV.CoupledFinalAnalytic.analytic_ray_from1250,common++whole)] do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut parents : Std.HashMap Name Name := {}
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing actual constant {name}"
      for prefix in forbiddenPrefixes do
        if name.toString.startsWith prefix then
          throwError "Finite count/old-local shortcut on analytic path: {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Admitted/native execution leaf: {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard actual dependency axiom: {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          parents := parents.insert dependency name
          pending := dependency::pending
    for name in required do
      unless seen.contains name do
        throwError "Required actual coupled path absent in {root}: {name}"
      let mut path := [name]
      let mut next := name
      while next != root do
        let some previous := parents[next]? | throwError "Broken actual dependency path"
        path := previous::path
        next := previous
      logInfo m!"CHECKED_COUPLED_PATH {root}: {String.intercalate " -> " (path.map toString)}"
    for prefix in forbiddenPrefixes do
      logInfo m!"ABSENT_FINITE_NAMESPACE {root}: {prefix}"
    logInfo m!"COMPLETE_COUPLED_CONSTANT_CLOSURE {root} {seen.size}"
    logInfo m!"COMPLETE_COUPLED_AXIOM_UNIVERSE {root} {axioms.toList}"

namespace RamanujanPV.CoupledFinalIndependentAudit
open Real Set AnalyticTransition
set_option autoImplicit false

/-- Exact paper Eq(1.6), including one-sided sign and the closed1423..1e19 domain. -/
example : CoupledActualPi.ButheThetaUpper ↔
    ∀t:ℝ,1423≤t→t≤10000000000000000000→
      t-Chebyshev.theta t≤(39/20:ℝ)*Real.sqrt t := by
  constructor
  · intro h t hlo hhi
    exact h t ⟨hlo,hhi⟩
  · intro h t ht
    exact h t ht.1 ht.2

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

example {x : ℝ} (hx : (1250000000000:ℝ)≤x) : (9005:ℝ)<gap x :=
  CoupledFinalAnalytic.analytic_ray_gap9005_from1250 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
    htheta hlower hupper hx

example {x : ℝ} (hx : (1250000000000:ℝ)≤x) :
    IEANTN.primeCounting x ^ 2 < exp 1*x/log x*IEANTN.primeCounting (x/exp 1) :=
  CoupledFinalAnalytic.analytic_ray_from1250 hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
    htheta hlower hupper hx
end OriginalInputs

#print axioms CoupledFinalAnalytic.analytic_ray_gap9005_from1250
#print axioms CoupledFinalAnalytic.analytic_ray_from1250
#print axioms CoupledAnalyticStrip.gap9005
end RamanujanPV.CoupledFinalIndependentAudit
