/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import PopulationActualConsumers
import PopulationMatchedControl
import IEANTN.Nodes.RH.v1.Conclusions
open Lean Elab Command

private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

private partial def applicationClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root::rest, seen =>
    if seen.contains root then applicationClosure env rest seen else
    let seen := root::seen
    if !(root.toString.startsWith "RH080Next." || root.toString.startsWith "RHOnePrime." ||
      root.toString.startsWith "GoldbachDirect." || root.toString.startsWith "IEANTN." ||
      root.toString.startsWith "AffineFourierPrograms." ||
      root.toString.startsWith "RHWeightedPopulation." || root.toString.startsWith "BRFourierInput.") then
      applicationClosure env rest seen
    else match env.find? root with
      | none => applicationClosure env rest seen
      | some info =>
        let constants := info.type.getUsedConstants
        let constants := match info with
          | .thmInfo value => constants ++ value.value.getUsedConstants
          | .defnInfo value => constants ++ value.value.getUsedConstants
          | _ => constants
        applicationClosure env (constants.toList ++ rest) seen

example : RH.v1.hypothesis = RiemannHypothesis := rfl
example : BRFourierInput.v1.norm_identity = RH080Next.Explicit.SourceBRFourierNormFive := rfl
example : BRFourierInput.v1.uniform_population_q1 =
    RH080Next.Explicit.SourceBRUniformPopulationQ1 := rfl
example : AffineFourierPrograms.v1.sparseNodes = RH080Next.PopulationPV.nodes := rfl
example : AffineFourierPrograms.v1.flatNodes = RH080Next.FlatPopulationPV.nodes := rfl
example : BRFourierInput.v1.norm_identity → AffineFourierPrograms.v1.sparse_witness :=
  AffineFourierPrograms.v1.challenge_sparse_witness
example : BRFourierInput.v1.norm_identity → AffineFourierPrograms.v1.flat_witness :=
  AffineFourierPrograms.v1.challenge_flat_witness
example : BRFourierInput.v1.uniform_population_q1 → RH.v1.hypothesis →
    AffineFourierPrograms.v1.sparse_witness → RHWeightedPopulation.v1.sparse_curve :=
  RHWeightedPopulation.v1.challenge_sparse_curve
example : BRFourierInput.v1.uniform_population_q1 → RH.v1.hypothesis →
    AffineFourierPrograms.v1.flat_witness → RHWeightedPopulation.v1.flat_curve :=
  RHWeightedPopulation.v1.challenge_flat_curve
example : BRFourierInput.v1.norm_identity → BRFourierInput.v1.uniform_population_q1 →
    RH.v1.hypothesis → RHWeightedPopulation.v1.frontier_count :=
  RH080Next.PopulationCanonical.source_first_frontier_count

run_cmd do
  let env ← getEnv
  let roots := #[
    `AffineFourierPrograms.v1.challenge_sparse_witness,
    `AffineFourierPrograms.v1.challenge_flat_witness,
    `RHWeightedPopulation.v1.challenge_sparse_curve,
    `RHWeightedPopulation.v1.challenge_flat_curve,
    `RHWeightedPopulation.v1.challenge_frontier_curve,
    `RHWeightedPopulation.v1.challenge_frontier_count,
    `RHWeightedPopulation.v1.challenge_one_population,
    `RHWeightedPopulation.v1.challenge_ten_population,
    `RHWeightedPopulation.v1.challenge_below_octic_leading_frontier,
    `RH080Next.PopulationCanonical.source_first_sparse_curve,
    `RH080Next.PopulationCanonical.source_first_flat_curve,
    `RH080Next.PopulationCanonical.source_first_frontier,
    `RH080Next.PopulationCanonical.source_first_frontier_count,
    `RH080Next.PopulationCanonical.source_first_one_population,
    `RH080Next.PopulationCanonical.source_first_ten_population,
    `RH080Next.PopulationCanonical.kernel_only_sparse_witness,
    `RH080Next.PopulationCanonical.kernel_only_flat_witness,
    `RH080Next.PopulationCanonical.kernel_only_frontier]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted axiom {root}: {axioms}"
    logInfo m!"POPULATION_CANONICAL_AXIOMS {root}: {axioms}"
    if root == `RHWeightedPopulation.v1.challenge_sparse_curve ||
       root == `RHWeightedPopulation.v1.challenge_flat_curve then
      for parameter in ["hUniform","hRH","hProvider"] do
        unless (leadingUses info.value).any (fun p => p.1==parameter && p.2) do
          throwError "Source/RH/witness input not consumed {root}:{parameter}"
  let sourceRoots := [
    `RH080Next.PopulationCanonical.source_first_frontier_count,
    `RH080Next.PopulationCanonical.source_first_one_population,
    `RH080Next.PopulationCanonical.source_first_ten_population]
  let sourceClosure := applicationClosure env sourceRoots []
  for required in #[
    `RH080Next.PopulationPV.actual_source_output,
    `RH080Next.PopulationPV.actual_source_syntax,
    `RH080Next.PopulationPV.actual_main_output,
    `RH080Next.PopulationPV.source_first_periodic_norm,
    `RH080Next.FlatPopulationPV.actual_source_output,
    `RH080Next.FlatPopulationPV.actual_source_syntax,
    `RH080Next.FlatPopulationPV.actual_main_output,
    `RH080Next.FlatPopulationPV.source_first_periodic_norm,
    `RH080Next.PopulationWitness.actual_eligible,
    `RH080Next.FlatPopulationWitness.actual_eligible,
    `RH080Next.PopulationWitness.actual_positive_leakage,
    `RH080Next.FlatPopulationWitness.actual_positive_leakage,
    `RH080Next.Explicit.source_BR_population_goodCoefficient,
    `RHOnePrime.CMSFunctional.eventual_count_of_good] do
    unless sourceClosure.contains required do throwError "Actual source/math provider missing {required}"
  for forbidden in #[
    `RH080Next.PopulationPV.kernel_only_periodic_norm,
    `RH080Next.FlatPopulationPV.kernel_only_periodic_norm] do
    if sourceClosure.contains forbidden then throwError "Source proof uses kernel-only shortcut {forbidden}"
  let controlClosure := applicationClosure env [`RH080Next.PopulationCanonical.kernel_only_frontier] []
  for required in #[`RH080Next.PopulationPV.kernel_only_periodic_norm,
    `RH080Next.FlatPopulationPV.kernel_only_periodic_norm,
    `RH080Next.Explicit.source_BR_population_goodCoefficient] do
    unless controlClosure.contains required do throwError "Matched control provider missing {required}"
  for forbidden in #[
    `RH080Next.PopulationPV.actual_source_output,
    `RH080Next.PopulationPV.actual_source_syntax,
    `RH080Next.PopulationPV.actual_main_output,
    `RH080Next.PopulationPV.source_first_periodic_norm,
    `RH080Next.FlatPopulationPV.actual_source_output,
    `RH080Next.FlatPopulationPV.actual_source_syntax,
    `RH080Next.FlatPopulationPV.actual_main_output,
    `RH080Next.FlatPopulationPV.source_first_periodic_norm] do
    if controlClosure.contains forbidden then throwError "Matched control consumes source execution {forbidden}"
  logInfo m!"POPULATION_CANONICAL_SOURCE_CLOSURE_PASS visited={sourceClosure.length}"
  logInfo m!"POPULATION_CANONICAL_CONTROL_CLOSURE_PASS visited={controlClosure.length}"
  logInfo "POPULATION_CANONICAL_AUDIT_PASS roots=18 exact_inputs=2 exact_sources=2"
