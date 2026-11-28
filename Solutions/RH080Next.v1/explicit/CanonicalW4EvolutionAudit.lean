/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalW4ActualConsumers
import IEANTN.Nodes.RH.v1.Conclusions
import Lean

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
open Lean Elab Command Meta

-- These are exact old conclusions, not weaker replacements.
example : RHWeightedPopulation.v2.sparse_curve =
    RHWeightedPopulation.v1.sparse_curve := rfl
example : RHWeightedPopulation.v2.flat_curve =
    RHWeightedPopulation.v1.flat_curve := rfl
example : RHWeightedPopulation.v2.frontier_curve =
    RHWeightedPopulation.v1.frontier_curve := rfl
example : RHWeightedPopulation.v2.frontier_count =
    RHWeightedPopulation.v1.frontier_count := rfl
example : RHWeightedPopulation.v2.one_population =
    RHWeightedPopulation.v1.one_population := rfl
example : RHWeightedPopulation.v2.ten_population =
    RHWeightedPopulation.v1.ten_population := rfl
example : RHWeightedPopulation.v2.below_octic_leading_frontier =
    RHWeightedPopulation.v1.below_octic_leading_frontier := rfl

/-- Follow actual proof values. The numerical leaf modules already have a
complete typed/axiom audit. Only this source-path walk stops at their data;
the complete kernel axiom union below has no such stopping condition. -/
private partial def proofClosure (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | name :: rest, seen =>
    if seen.contains name then proofClosure env rest seen else
    let seen := seen.insert name
    if name.toString.startsWith "W4DAG24.W4D24" ||
        name.toString.startsWith "_private.W4D24" then proofClosure env rest seen else
    let relevant := ["RH080Next.", "W4DAG24.", "FapForest17.", "GoldbachDirect.",
      "_private.", "W4FourierNorm.", "RHGlobalAffineIntervals.",
      "RHAnalyticFlatPopulation.", "RHWeightedPopulation.", "CMSZeroSummation.",
      "FapFourierNorm.", "RHFiniteAffineIntervals."]
    if !(relevant.any fun initial => name.toString.startsWith initial) then
      proofClosure env rest seen
    else match env.find? name with
    | none => proofClosure env rest seen
    | some info =>
      let used := match info with
        | .thmInfo t => t.value.getUsedConstants
        | .defnInfo t => t.value.getUsedConstants
        | .opaqueInfo t => t.value.getUsedConstants
        | _ => #[]
      proofClosure env (used.toList ++ rest) seen

run_cmd liftTermElabM do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let edges : Array (Name × Array Name × Name) := #[
    (`W4FourierNorm.v1.challenge_l1_bound,
      #[`BRFourierInput.v1.norm_identity],
      `W4FourierNorm.v1.l1_bound),
    (`RHGlobalAffineIntervals.v1.challenge_global_0851062,
      #[
        `CMSExplicitInputs.v1.strip_regularity,
        `CMSExplicitInputs.v1.guinand_weil,
        `CMSExplicitInputs.v1.digamma_integral,
        `CMSExplicitInputs.v1.real_eta_integral,
        `CMSExplicitInputs.v1.zero_counting,
        `CMSZeroSummation.v1.partial_summation,
        `CMSExplicitInputs.v1.montgomery_vaughan,
        `CMSExplicitInputs.v1.historical_finite_gap,
        `W4FourierNorm.v1.l1_bound,
        `RH.v1.hypothesis
      ],
      `RHGlobalAffineIntervals.v1.global_0851062),
    (`RHGlobalAffineIntervals.v1.challenge_branch_0777,
      #[`RHFiniteAffineIntervals.v2.interval_0777_small],
      `RHGlobalAffineIntervals.v1.branch_0777),
    (`RHGlobalAffineIntervals.v1.challenge_branch_074,
      #[`RHFiniteAffineIntervals.v2.interval_074_full],
      `RHGlobalAffineIntervals.v1.branch_074),
    (`RHGlobalAffineIntervals.v1.challenge_branch_075,
      #[`RHFiniteAffineIntervals.v2.interval_075_full],
      `RHGlobalAffineIntervals.v1.branch_075),
    (`RHGlobalAffineIntervals.v1.challenge_branch_08,
      #[`RHFiniteAffineIntervals.v2.interval_08_full],
      `RHGlobalAffineIntervals.v1.branch_08),
    (`RHGlobalAffineIntervals.v1.challenge_branch_0851062,
      #[`RHGlobalAffineIntervals.v1.global_0851062],
      `RHGlobalAffineIntervals.v1.branch_0851062),
    (`RHGlobalAffineIntervals.v1.challenge_piecewise_strict,
      #[
        `RHGlobalAffineIntervals.v1.branch_0777,
        `RHGlobalAffineIntervals.v1.branch_074,
        `RHGlobalAffineIntervals.v1.branch_075,
        `RHGlobalAffineIntervals.v1.branch_08,
        `RHGlobalAffineIntervals.v1.branch_0851062
      ],
      `RHGlobalAffineIntervals.v1.piecewise_strict),
    (`RHAnalyticFlatPopulation.v1.challenge_family_curve,
      #[
        `BRFourierInput.v1.norm_identity,
        `BRFourierInput.v1.uniform_population_q1,
        `RH.v1.hypothesis
      ],
      `RHAnalyticFlatPopulation.v1.family_curve),
    (`RHAnalyticFlatPopulation.v1.challenge_family_infimum,
      #[`RHAnalyticFlatPopulation.v1.family_curve],
      `RHAnalyticFlatPopulation.v1.family_infimum),
    (`RHAnalyticFlatPopulation.v1.challenge_flat64_curve,
      #[
        `BRFourierInput.v1.norm_identity,
        `BRFourierInput.v1.uniform_population_q1,
        `RH.v1.hypothesis
      ],
      `RHAnalyticFlatPopulation.v1.flat64_curve),
    (`RHAnalyticFlatPopulation.v1.challenge_forty_population,
      #[`RHAnalyticFlatPopulation.v1.flat64_curve],
      `RHAnalyticFlatPopulation.v1.forty_population),
    (`RHAnalyticFlatPopulation.v1.challenge_adaptive_limit,
      #[],
      `RHAnalyticFlatPopulation.v1.adaptive_limit),
    (`RHAnalyticFlatPopulation.v1.challenge_adaptive_population,
      #[`RHAnalyticFlatPopulation.v1.family_curve, `RHAnalyticFlatPopulation.v1.adaptive_limit],
      `RHAnalyticFlatPopulation.v1.adaptive_population),
    (`RHWeightedPopulation.v2.challenge_sparse_curve,
      #[`RHWeightedPopulation.v1.sparse_curve],
      `RHWeightedPopulation.v2.sparse_curve),
    (`RHWeightedPopulation.v2.challenge_flat_curve,
      #[`RHWeightedPopulation.v1.flat_curve],
      `RHWeightedPopulation.v2.flat_curve),
    (`RHWeightedPopulation.v2.challenge_frontier_curve,
      #[`RHWeightedPopulation.v1.frontier_curve],
      `RHWeightedPopulation.v2.frontier_curve),
    (`RHWeightedPopulation.v2.challenge_frontier_count,
      #[`RHWeightedPopulation.v1.frontier_count],
      `RHWeightedPopulation.v2.frontier_count),
    (`RHWeightedPopulation.v2.challenge_one_population,
      #[`RHWeightedPopulation.v1.one_population],
      `RHWeightedPopulation.v2.one_population),
    (`RHWeightedPopulation.v2.challenge_ten_population,
      #[`RHWeightedPopulation.v1.ten_population],
      `RHWeightedPopulation.v2.ten_population),
    (`RHWeightedPopulation.v2.challenge_below_octic_leading_frontier,
      #[`RHWeightedPopulation.v1.below_octic_leading_frontier],
      `RHWeightedPopulation.v2.below_octic_leading_frontier),
    (`RHWeightedPopulation.v2.challenge_w4_curve,
      #[
        `CMSExplicitInputs.v1.strip_regularity,
        `CMSExplicitInputs.v1.guinand_weil,
        `CMSExplicitInputs.v1.digamma_integral,
        `CMSExplicitInputs.v1.real_eta_integral,
        `CMSExplicitInputs.v1.zero_counting,
        `CMSZeroSummation.v1.partial_summation,
        `CMSExplicitInputs.v1.montgomery_vaughan,
        `W4FourierNorm.v1.l1_bound,
        `RH.v1.hypothesis
      ],
      `RHWeightedPopulation.v2.w4_curve),
    (`RHWeightedPopulation.v2.challenge_w4_infimum_strict,
      #[
        `CMSExplicitInputs.v1.strip_regularity,
        `CMSExplicitInputs.v1.guinand_weil,
        `CMSExplicitInputs.v1.digamma_integral,
        `CMSExplicitInputs.v1.real_eta_integral,
        `CMSExplicitInputs.v1.zero_counting,
        `CMSZeroSummation.v1.partial_summation,
        `CMSExplicitInputs.v1.montgomery_vaughan,
        `W4FourierNorm.v1.l1_bound,
        `RH.v1.hypothesis
      ],
      `RHWeightedPopulation.v2.w4_infimum_strict),
    (`RHWeightedPopulation.v2.challenge_three_frontier_curve,
      #[
        `RHWeightedPopulation.v2.w4_curve,
        `RHWeightedPopulation.v1.sparse_curve,
        `RHWeightedPopulation.v1.flat_curve
      ],
      `RHWeightedPopulation.v2.three_frontier_curve),
    (`RHWeightedPopulation.v2.challenge_actual_below_both_printed_lines,
      #[`RHWeightedPopulation.v2.three_frontier_curve],
      `RHWeightedPopulation.v2.actual_below_both_printed_lines),
    (`RHWeightedPopulation.v2.challenge_four_frontier_curve,
      #[`RHWeightedPopulation.v2.three_frontier_curve, `RHAnalyticFlatPopulation.v1.flat64_curve],
      `RHWeightedPopulation.v2.four_frontier_curve),
    (`RHWeightedPopulation.v2.challenge_four_frontier_count,
      #[`RHWeightedPopulation.v2.four_frontier_curve],
      `RHWeightedPopulation.v2.four_frontier_count),
    (`RHWeightedPopulation.v2.challenge_adaptive_frontier_curve,
      #[
        `RHWeightedPopulation.v2.four_frontier_curve,
        `RHAnalyticFlatPopulation.v1.adaptive_population
      ],
      `RHWeightedPopulation.v2.adaptive_frontier_curve),
    (`RHWeightedPopulation.v2.challenge_adaptive_frontier_count,
      #[`RHWeightedPopulation.v2.adaptive_frontier_curve],
      `RHWeightedPopulation.v2.adaptive_frontier_count)
  ]
  unless edges.size == 29 do throwError "Canonical claim inventory differs"
  for (root, premises, target) in edges do
    let some (.thmInfo info) := env.find? root |
      throwError "Missing canonical edge proof {root}"
    let mut expected := mkConst target
    for premise in premises.toList.reverse do
      expected := mkForall Name.anonymous BinderInfo.default (mkConst premise) expected
    unless (← isDefEq info.type expected) do
      throwError "Exact metadata conditional type differs {root}"
    lambdaTelescope info.value fun params body => do
      unless premises.size ≤ params.size do
        throwError "Missing metadata assumption binders {root}"
      for i in [:premises.size] do
        unless body.containsFVar params[i]!.fvarId! do
          throwError "Canonical graph import is not used by actual proof {root}: {i}"

  let common := #[`BRFourierInput.v1.norm_identity,
    `CMSExplicitInputs.v1.strip_regularity, `CMSExplicitInputs.v1.guinand_weil,
    `CMSExplicitInputs.v1.digamma_integral, `CMSExplicitInputs.v1.real_eta_integral,
    `CMSExplicitInputs.v1.zero_counting, `CMSExplicitInputs.v1.montgomery_vaughan,
    `RH.v1.hypothesis]
  let intervalPremises := common.push `CMSExplicitInputs.v1.historical_finite_gap
  let populationPremises := common.push `BRFourierInput.v1.uniform_population_q1
  let actual : Array (Name × Array Name × Expr) := #[
    (`RH080Next.CanonicalW4.source_first_global, intervalPremises,
      mkConst `RHGlobalAffineIntervals.v1.global_0851062),
    (`RH080Next.CanonicalW4.source_first_five_branches, intervalPremises,
      mkApp2 (mkConst ``And) (mkConst `RHGlobalAffineIntervals.v1.branch_0777)
        (mkApp2 (mkConst ``And) (mkConst `RHGlobalAffineIntervals.v1.branch_074)
          (mkApp2 (mkConst ``And) (mkConst `RHGlobalAffineIntervals.v1.branch_075)
            (mkApp2 (mkConst ``And) (mkConst `RHGlobalAffineIntervals.v1.branch_08)
              (mkConst `RHGlobalAffineIntervals.v1.branch_0851062))))),
    (`RH080Next.CanonicalW4.source_first_piecewise, intervalPremises,
      mkConst `RHGlobalAffineIntervals.v1.piecewise_strict),
    (`RH080Next.CanonicalW4.source_first_w4_curve, common,
      mkConst `RHWeightedPopulation.v2.w4_curve),
    (`RH080Next.CanonicalW4.source_first_w4_infimum_strict, common,
      mkConst `RHWeightedPopulation.v2.w4_infimum_strict),
    (`RH080Next.CanonicalW4.source_first_three_frontier, populationPremises,
      mkConst `RHWeightedPopulation.v2.three_frontier_curve),
    (`RH080Next.CanonicalW4.hybrid_four_frontier, populationPremises,
      mkConst `RHWeightedPopulation.v2.four_frontier_curve),
    (`RH080Next.CanonicalW4.hybrid_adaptive_frontier, populationPremises,
      mkConst `RHWeightedPopulation.v2.adaptive_frontier_curve),
    (`RH080Next.CanonicalW4.hybrid_adaptive_count, populationPremises,
      mkConst `RHWeightedPopulation.v2.adaptive_frontier_count)
  ]
  for (root, premises, target) in actual do
    let some (.thmInfo info) := env.find? root |
      throwError "Missing fully composed canonical consumer {root}"
    let mut expected := target
    for premise in premises.toList.reverse do
      expected := mkForall Name.anonymous BinderInfo.default (mkConst premise) expected
    unless (← isDefEq info.type expected) do
      throwError "Final consumer retained or changed its exact named premises {root}"

  -- Kernel-check a real And proof containing all38 actual theorem constants.
  -- Its full axiom union bounds every component's axiom set; no per-root
  -- equality of axiom sets is inferred or printed.
  let roots := (edges.map fun (root, _, _) => root) ++
    (actual.map fun (root, _, _) => root)
  unless roots.size == 38 do throwError "Final canonical root inventory differs"
  let last := roots.back!
  let some lastInfo := env.find? last | throwError "Missing final component"
  unless lastInfo.levelParams.isEmpty do throwError "Unexpected component universes"
  let mut bundleType := lastInfo.type
  let mut bundleValue := mkConst last
  for root in roots.toList.reverse.tail do
    let some info := env.find? root | throwError "Missing aggregate proof {root}"
    unless info.levelParams.isEmpty do throwError "Unexpected proof universes"
    bundleValue := mkApp4 (mkConst ``And.intro) info.type bundleType
      (mkConst root) bundleValue
    bundleType := mkApp2 (mkConst ``And) info.type bundleType
  let bundleName := `RH080Next.CanonicalW4Audit.selected_proof_bundle
  liftM (m := CoreM) (n := TermElabM) <| addDecl (.thmDecl {
    name := bundleName, levelParams := [], type := bundleType, value := bundleValue })
  let checkedEnv ← getEnv
  let some (.thmInfo bundle) := checkedEnv.find? bundleName |
    throwError "Kernel-checked aggregate proof absent"
  for root in roots do
    unless bundle.value.getUsedConstants.contains root do
      throwError "Aggregate omitted actual proof component {root}"
  let axes ← collectAxioms bundleName
  unless axes.all allowed.contains do
    throwError "Nonstandard final canonical proof axiom: {axes}"
  logInfo m!"CANONICAL_W4_AGGREGATE_AXIOM_UNION roots={roots.size} axioms={axes}"
  for root in roots do
    logInfo m!"CANONICAL_W4_EVOLUTION_AXIOMS {root} subset_of_checked_union={axes}"

  let sourceRoots := #[`W4FourierNorm.v1.challenge_l1_bound] ++
    (actual.map fun (root, _, _) => root)
  for root in sourceRoots do
    let used := proofClosure env [root] {}
    for required in #[`RH080Next.FFTPV.W4Main.source_first_actual_norm,
      `RH080Next.FFTPV.W4Main.actual_main_result,
      `RH080Next.FFTPV.W4Main.main_output_actual_norm,
      `RH080Next.FFTPV.MainIO.result_value_eq,
      `RH080Next.FFTPV.MainIO.actual_result,
      `RH080Next.FFTPV.MainIO.every_main_call,
      `RH080Next.FFTPV.MainIO.actual_main_success,
      `RH080Next.FFTPV.MainIO.source_main_call,
      `RH080Next.FFTPV.MainIO.every_printf_arguments,
      `RH080Next.FFTPV.MainIO.main_body,
      `RH080Next.FFTPV.MainSuffix.norm_call_exists,
      `RH080Next.FFTPV.MainSuffix.every_norm_call,
      `RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.MainCertificate.w4Certificate,
      `W4DAG24.complete_execution, `W4DAG24.total_checked, `W4DAG24.quad_checked] do
      unless used.contains required do
        throwError "Missing actual W4 source/main/numerical proof dependency {root}: {required}"
    if root != `W4FourierNorm.v1.challenge_l1_bound then
      unless used.contains `RH080Next.Explicit.cms_zero_partial_summation_kernel do
        throwError "Final prime consumer omits proved zero kernel {root}"
    logInfo m!"CANONICAL_W4_SOURCE_ROOT {root} proof_value_closure={used.toList.length}"
  for root in #[`RH080Next.CanonicalW4.source_first_five_branches,
      `RH080Next.CanonicalW4.source_first_piecewise] do
    let used := proofClosure env [root] {}
    for required in #[`RH080Next.FFTPV.FapMain.source_first_actual_norm,
      `RH080Next.FFTPV.FapMain.actual_main_result,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax] do
      unless used.contains required do
        throwError "Piecewise consumer omits actual finite C provider {root}: {required}"
  for root in #[`RH080Next.CanonicalW4.source_first_three_frontier,
      `RH080Next.CanonicalW4.hybrid_four_frontier,
      `RH080Next.CanonicalW4.hybrid_adaptive_frontier,
      `RH080Next.CanonicalW4.hybrid_adaptive_count] do
    let used := proofClosure env [root] {}
    for required in #[`RH080Next.PopulationCanonical.source_first_sparse_curve,
      `RH080Next.PopulationCanonical.source_first_flat_curve] do
      unless used.contains required do
        throwError "Population consumer omits actual short-profile C provider {root}: {required}"
  logInfo ("CANONICAL_W4_EVOLUTION_AUDIT_PASS claims=29 roots=38 " ++
    "exact-types all-imports-used full-source-main-and-N24 kernel-zero " ++
    "original-v1-preserved Std3 no-native aggregate-axiom-superset")
