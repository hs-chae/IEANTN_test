/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FullSourceResult
import Lean.Util.FoldConsts

/-! Complete separate proof/type closure inspection of the full original-row
source result and its explicitly conditional global consumer. No theorem is
proved by native numerical evaluation here. The inspection fails on missing
source paths, old scalar/local shortcuts, or any nonstandard axiom. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let common : List Name := [
    `RamanujanPV.FullSourceResult.actual_program_bindings,
    `RamanujanPV.FullSourceResult.ActualProgramBindings,
    `RamanujanPV.QuotientCSource.actual_source_checked,
    `RamanujanPV.FiniteExpSource.actual_source_checked,
    `RamanujanPV.FiniteLogSource.actual_source_checked,
    `RamanujanPV.FiniteCellSource.actual_source_checked,
    `RamanujanPV.FullAdaptiveSourcePV.all_source_margins,
    `RamanujanPV.FullFiniteSourcePV.checked_block_source,
    `RamanujanPV.FullFiniteSourcePV.row_source,
    `RamanujanPV.FullFiniteSourcePV.log_source,
    `RamanujanPV.FullFiniteSourcePV.source_enclosures,
    `RamanujanPV.FiniteCellGeneric.source_execution_from_math,
    `RamanujanPV.FiniteCellGeneric.positive_implies_strict,
    `RamanujanPV.FiniteCellGeneric.reference_run,
    `RamanujanPV.FiniteCellGeneric.service_closed,
    `RamanujanPV.FiniteLogUpperExecute.source_execution_from_math,
    `RamanujanPV.FiniteLogUpperExecute.function_executes,
    `RamanujanPV.FiniteLogUpperExecute.completed_correct,
    `RamanujanPV.FiniteLogUpperExecute.source_log_upper_sound,
    `RamanujanPV.FiniteLogSeriesExecute.function_executes,
    `RamanujanPV.FiniteLogSeriesExecute.service_closed,
    `RamanujanPV.FiniteLogSeriesLoop.loop_exec,
    `RamanujanPV.FiniteLogSeriesInit.z_declare,
    `RamanujanPV.FiniteLogSeriesInit.z2_declare,
    `RamanujanPV.FiniteLogSeriesReturn.return_eval,
    `RamanujanPV.FiniteLogNormalize.normalization_exec,
    `RamanujanPV.FiniteLogServices.ceil_service_closed,
    `RamanujanPV.FiniteLogCeil.function_executes,
    `RamanujanPV.FiniteWideExpLinked.service_closed,
    `RamanujanPV.FiniteWideExpExecute.low_source_run,
    `RamanujanPV.FiniteWideExpEnclosures.source_e_scaled,
    `RamanujanPV.FiniteScalarMachine.eval,
    `RamanujanPV.WideScalar.binary]
  let conditional : List Name := [
    `RamanujanPV.FullSourceResult.RemainingCountExecutions,
    `RamanujanPV.SourceGlobalAssembly.all_real_gap9005_from_completed_counts,
    `RamanujanPV.AnalyticMargin.analytic_ray_gap9005,
    `RamanujanPV.FullFiniteSourcePV.gap_from_source_counts,
    `RamanujanPV.FullFiniteSourcePV.complete_from_source_counts,
    `RamanujanPV.FullFiniteScalars.complete_from_counts,
    `RamanujanPV.QuotientCCell.SourceExecution,
    `RamanujanPV.QuotientCCell.source_execution_count,
    `RamanujanPV.QuotientCFunction.LinkedCountRun,
    `RamanujanPV.QuotientCFunction.completed_execution_correct,
    `RamanujanPV.QuotientCFunction.function_refines,
    `RamanujanPV.QuotientCWhole.outer_for_exec,
    `RamanujanPV.QuotientCInit.initialization_loop,
    `RamanujanPV.QuotientCSmallLoop.small_branch_exec,
    `RamanujanPV.QuotientSqrtExecute.service,
    `RamanujanPV.QuotientSieve.total_final]
  let forbidden : List Name := [
    `RamanujanPV.FullFiniteScalars.scalar_sound,
    `RamanujanPV.FullAdaptiveScalars.all_scalars,
    `RamanujanPV.FiniteGuardedResult.source_linked_uniform_gap,
    `RamanujanPV.FiniteGuardedMillion.uniform_gap,
    `RamanujanPV.FiniteGuardedMillion.complete_certificate,
    `RamanujanPV.FiniteProgramMillion.complete_certificate,
    `RamanujanPV.FiniteSourceRamanujanMillion.complete_certificate,
    `RamanujanPV.MillionCriticalSourceClosed.real_interval,
    `RamanujanPV.CriticalSourceClosed.first_1001_real_interval,
    `RamanujanPV.SegmentRamanujanMillion.complete_certificate,
    `RamanujanPV.SegmentSourceMargins.million_gap,
    `RamanujanPV.LocalCellsMillion.checked,
    `RamanujanPV.LocalCellsMillion.conditional_certificate,
    `RamanujanPV.WindowCells.row_counts,
    `RamanujanPV.WindowCells.row_real_enclosures,
    `RamanujanPV.WindowCells.complete_certificate,
    `RamanujanPV.PrimeWindow.count_at,
    `RamanujanPV.PrimeWindow.source_count_at,
    `RamanujanPV.LocalWindowMillion.p_increment,
    `RamanujanPV.LocalWindowMillion.q_increment]
  let roots : List (Name × List Name) := [
    (`RamanujanPV.FullSourceResult.all_scalar_programs,common),
    (`RamanujanPV.FullSourceResult.all_real_gap9005_if_counts_completed,common++conditional)]
  for (root,required) in roots do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut parent : Std.HashMap Name Name := {}
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing inspected constant {name}"
      if name == `Lean.ofReduceBool || name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Forbidden native/admitted proof leaf: {name}"
      if name.toString.startsWith "RamanujanPV.FiniteScalarMillion.cell_domain_" then
        throwError "Old local guard-domain numerical provider: {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard axiom in actual proof/type closure: {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          parent := parent.insert dependency name
          pending := dependency::pending
    let mut missing : List Name := []
    for name in required do
      if !seen.contains name then
        missing := name::missing
        logInfo m!"MISSING_REQUIRED {root}: {name}"
      else
        let mut path := [name]
        let mut next := name
        while next != root do
          let some previous := parent[next]? | throwError "Broken actual dependency path"
          path := previous::path
          next := previous
        logInfo m!"SOURCE_PATH {root}: {String.intercalate " -> " (path.map toString)}"
    for name in forbidden do
      if seen.contains name then
        throwError "Old scalar/local shortcut in {root}: {name}"
      logInfo m!"ABSENT_SHORTCUT {root}: {name}"
    logInfo m!"COMPLETE_CONSTANT_DEPENDENCY_INSPECTION {root} {seen.size}"
    logInfo m!"COMPLETE_AXIOM_UNIVERSE {root} {axioms.toList}"
    unless missing.isEmpty do
      throwError "Required source paths missing for {root}: {missing}"

namespace RamanujanPV.FullSourceDependencyAudit
open Real IEANTN AnalyticTransition
set_option autoImplicit false
example : FullSourceResult.ActualProgramBindings ∧
    FullFiniteSourcePV.SourceMarginCertificate 38358837683 1490000000001 9005
      FullAdaptiveSourcePV.allRows := FullSourceResult.all_scalar_programs

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

example (counts : FullSourceResult.RemainingCountExecutions) :
    FullSourceResult.ActualProgramBindings ∧
      ∀x:ℝ,(38358837683:ℝ)≤x→(9005:ℝ)<gap x :=
  FullSourceResult.all_real_gap9005_if_counts_completed hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh hFKS hRH hseries hoffset hpositive hbuthe hCH2 hDusart
    htheta hlower counts
end OriginalInputs
end RamanujanPV.FullSourceDependencyAudit
#print axioms RamanujanPV.FullSourceResult.all_scalar_programs
#print axioms RamanujanPV.FullSourceResult.all_real_gap9005_if_counts_completed
