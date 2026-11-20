/- Copyright (c) 2026 IEANTN contributors. Apache2.0. -/
import RamanujanPV.CoupledLargeMargin
import Lean.Util.FoldConsts

/-! Independent check of the stronger analytic margin only. The finite source
program's9005 margin, old source arrays and prior3-root audit are unchanged. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let root := `RamanujanPV.CoupledLargeMargin.analytic_ray_gap_six_trillion
  let required : List Name := [
    `IEANTN.primeCounting,`Nat.primeCounting,`IEANTN.li,`RamanujanPV.gap,
    `RamanujanPV.CoupledActualPi.ButheThetaUpper,
    `RamanujanPV.CoupledLargeMargin.strip_gap_large,
    `RamanujanPV.CoupledLargeMargin.actual_bridge_gap_large,
    `RamanujanPV.CoupledLargeMargin.bridge_gap_large,
    `RamanujanPV.CoupledLargeMargin.quantitative_expression_large,
    `RamanujanPV.CoupledAnalyticStrip.normalized_margin,
    `RamanujanPV.CoupledBaseEnvelope.endpoint_positive,
    `RamanujanPV.CoupledScalarComparison.comparison,
    `RamanujanPV.CoupledActualPi.actual_pi_identity,
    `RamanujanPV.CoupledActualPi.shared_upper,
    `RamanujanPV.CoupledUniformBounds.Uerr_uniform,
    `RamanujanPV.AnalyticTransition.improvedEnvelope_margin,
    `RamanujanPV.FinalAnalytic.quantitative_from40,
    `RamanujanPV.QRHFullTail.pi_two_sided_144]
  let forbidden := ["RamanujanPV.HighTransitionCount.","RamanujanPV.DemandCriticalPair.",
    "RamanujanPV.LocalWindowMillion.","RamanujanPV.LocalCellsMillion.",
    "RamanujanPV.FiniteGuardedMillion.","RamanujanPV.FiniteGuardedResult.",
    "RamanujanPV.FullAdaptiveSourcePV.","RamanujanPV.FullSourceResult.",
    "RamanujanPV.SourceGlobalAssembly."]
  let some rootInfo := env.find? root | throwError "Missing actual larger-margin theorem"
  let rec binderNames : Expr → List Name
    | .forallE name _ body _ => name :: binderNames body
    | _ => []
  let names := binderNames rootInfo.type
  unless names.length == 27 do
    throwError "Larger-margin theorem must have25sourceinputs+x+domain: {names}"
  logInfo m!"EXACT_LARGE_MARGIN_INPUT_BINDERS {names}"
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut parents : Std.HashMap Name Name := {}
  let mut pending := [root]
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    let some info := env.find? name | throwError "Missing actual constant {name}"
    for oldNamespace in forbidden do
      if name.toString.startsWith oldNamespace then
        throwError "Unexpected finite/local provider on pure analytic path: {name}"
    if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
      throwError "Admitted/native numerical leaf: {name}"
    match info with
    | .axiomInfo _ =>
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throwError "Unexpected source/kernel axiom: {name}"
      axioms := axioms.insert name
    | _ => pure ()
    for dependency in info.getUsedConstantsAsSet.toList do
      if !seen.contains dependency then
        seen := seen.insert dependency
        parents := parents.insert dependency name
        pending := dependency::pending
  for name in required do
    unless seen.contains name do
      throwError "Required actual larger-margin path absent: {name}"
    let mut path := [name]
    let mut next := name
    while next != root do
      let some previous := parents[next]? | throwError "Broken larger-margin dependency path"
      path := previous::path
      next := previous
    logInfo m!"LARGE_MARGIN_PATH {String.intercalate " -> " (path.map toString)}"
  for oldNamespace in forbidden do
    logInfo m!"LARGE_MARGIN_ABSENT_FINITE_NAMESPACE {oldNamespace}"
  logInfo m!"COMPLETE_LARGE_MARGIN_CONSTANT_CLOSURE {seen.size}"
  logInfo m!"COMPLETE_LARGE_MARGIN_AXIOM_UNIVERSE {axioms.toList}"

namespace RamanujanPV.CoupledLargeMarginIndependentAudit
open Real Set AnalyticTransition
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

example {x : ℝ} (hx : (1250000000000:ℝ) ≤ x) :
    (6000000000000:ℝ) <
      exp 1*x/log x*IEANTN.primeCounting (x/exp 1)-(IEANTN.primeCounting x)^2 :=
  CoupledLargeMargin.analytic_ray_gap_six_trillion hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
    htheta hlower hupper hx
end OriginalInputs

/-- Exact conservative arithmetic after scaling the existing normalized50 margin. -/
example : (6000000000000:ℝ) < 50*(27/10)*1250000000000/(281/10) := by norm_num
/-- Exact conservative arithmetic after scaling the old normalized90 margin. -/
example : (6000000000000:ℝ) < 90*(27/10)*1490000000000/44 := by norm_num
/-- Exact conservative height40 arithmetic using log^6(x)≤26x andx≥1e15. -/
example : (6000000000000:ℝ) < (37/5200)*1000000000000000 := by norm_num
#print axioms CoupledLargeMargin.analytic_ray_gap_six_trillion
#print axioms CoupledLargeMargin.strip_gap_large
#print axioms CoupledLargeMargin.actual_bridge_gap_large
#print axioms CoupledLargeMargin.quantitative_expression_large
end RamanujanPV.CoupledLargeMarginIndependentAudit
