/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Primal80WitnessSolution
import Primal80AsymptoticSolution
open Lean Elab Command MeasureTheory
open IEANTN.CMSFunctional

private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

private partial def applicationClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root::rest, seen =>
    if seen.contains root then applicationClosure env rest seen else
    let seen := root::seen
    if !(root.toString.startsWith "RHOnePrime." || root.toString.startsWith "RH080." ||
      root.toString.startsWith "GaussianFourierWitness." ||
      root.toString.startsWith "RHAsymptoticGaussian.") then
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

example : GaussianFourierWitness.v2.integral_fourier_witness :=
  GaussianFourierWitness.v2.challenge_integral_fourier_witness
example : GaussianFourierWitness.v2.objective_witness :=
  RH080.Primal80Gap.actual_objective_witness
example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis →
    EventualGapBound (2746403660/3293251743 : ℝ) :=
  RH080.Primal80Gap.actual_normalized_gap
example : CMSFunctionalInput.v1.population_reduction → RH.v1.hypothesis →
    RHAsymptoticGaussian.v2.population_curve := RH080.Primal80Gap.actual_population_curve
example : CMSFunctionalInput.v1.population_reduction → RH.v1.hypothesis →
    RHAsymptoticGaussian.v2.population_count := RH080.Primal80Gap.actual_population_count
example : GaussianFourierWitness.v2.integral_fourier_witness =
    (∃ F G : ℝ → ℝ, Eligible F G ∧ mass F ≤ (74901918/100000000 : ℝ) ∧
      positiveLeak G ≤ (3111791/100000000 : ℝ) ∧
      (999999999/1000000000 : ℝ) ≤ F 0) := rfl

run_cmd do
  let env ← getEnv
  let roots := #[
    `GaussianFourierWitness.v2.challenge_integral_fourier_witness,
    `GaussianFourierWitness.v2.challenge_objective_witness,
    `RHAsymptoticGaussian.v2.challenge_normalized_gap,
    `RHAsymptoticGaussian.v2.challenge_gap_below_readable,
    `RHAsymptoticGaussian.v2.challenge_gap_below_v1,
    `RHAsymptoticGaussian.v2.challenge_gap_below_printed_2026,
    `RHAsymptoticGaussian.v2.challenge_population_curve,
    `RHAsymptoticGaussian.v2.challenge_population_count,
    `RH080.Primal80Gap.actual_objective_witness,
    `RH080.Primal80Gap.actual_normalized_gap,
    `RH080.Primal80Gap.actual_gap_below_readable,
    `RH080.Primal80Gap.actual_gap_below_v1,
    `RH080.Primal80Gap.actual_gap_below_printed_2026,
    `RH080.Primal80Gap.actual_population_curve,
    `RH080.Primal80Gap.actual_population_count]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted axiom {root}: {axioms}"
    logInfo m!"PRIMAL80_CANONICAL_AXIOMS {root}: {axioms}"
    if root == `GaussianFourierWitness.v2.challenge_objective_witness then
      unless (leadingUses info.value).any (fun p => p.1=="hNumeric" && p.2) do
        throwError "Raw integral witness not consumed"
    if root == `RHAsymptoticGaussian.v2.challenge_normalized_gap ||
      root == `RHAsymptoticGaussian.v2.challenge_population_curve then
      for parameter in ["hCMS","rh","hNumeric"] do
        unless (leadingUses info.value).any (fun p => p.1==parameter && p.2) do
          throwError "Source/numerical input not consumed {root}:{parameter}"
  let edges := #[
    (`GaussianFourierWitness.v2.challenge_integral_fourier_witness,`RH080.Primal80Gap.gaussian_eligible),
    (`GaussianFourierWitness.v2.challenge_integral_fourier_witness,`RH080.Gaussian40.physical_norm_upper),
    (`GaussianFourierWitness.v2.challenge_integral_fourier_witness,`RH080.Gaussian40.physical_full_wings_upper),
    (`GaussianFourierWitness.v2.challenge_integral_fourier_witness,`RH080.Gaussian40.physicalF_zero_lower),
    (`RH080.Primal80Gap.gaussian_eligible,`RH080.Primal80Fourier.fourier_actual_physical),
    (`RHAsymptoticGaussian.v2.challenge_normalized_gap,`RHOnePrime.CMSFunctional.gap_from_functional),
    (`RHAsymptoticGaussian.v2.challenge_population_curve,`RHOnePrime.CMSFunctional.population_from_functional),
    (`RHAsymptoticGaussian.v2.challenge_population_count,`RHOnePrime.CMSFunctional.eventual_count_of_good),
    (`RH080.Primal80Gap.actual_objective_witness,`GaussianFourierWitness.v2.challenge_integral_fourier_witness),
    (`RH080.Primal80Gap.actual_objective_witness,`GaussianFourierWitness.v2.challenge_objective_witness),
    (`RH080.Primal80Gap.actual_normalized_gap,`RH080.Primal80Gap.actual_objective_witness),
    (`RH080.Primal80Gap.actual_population_curve,`RH080.Primal80Gap.actual_objective_witness)]
  for (root,dependency) in edges do
    let some (.thmInfo info) := env.find? root | throwError "Missing root {root}"
    unless info.value.getUsedConstants.contains dependency do
      throwError "Actual proof edge missing {root}->{dependency}"
  let closure := applicationClosure env roots.toList []
  for old in #[`RHOnePrime.GaussianKernel.normSource,`RHOnePrime.GaussianKernel.wingSource,
    `RHOnePrime.GaussianKernel.physicalF,`RHOnePrime.GaussianKernel.physicalG,
    `RHOnePrime.GaussianFourier.actual_even_transform,
    `RHOnePrime.GaussianFourier.fourier_actual_physical,
    `GaussianFourierWitness.v1.challenge_integral_fourier_witness] do
    if closure.contains old then throwError "Old actual witness consumed {old}"
  for required in #[`RH080.Gaussian40.normSource,`RH080.Gaussian40.wingSource,
    `RH080.Primal80Fourier.fourier_actual_physical,
    `RH080.Gaussian40.physical_norm_upper,`RH080.Gaussian40.physical_full_wings_upper] do
    unless closure.contains required do throwError "Required actual new provider absent {required}"
  logInfo m!"PRIMAL80_COMPLETE_NEW_SOURCE_CLOSURE_PASS visited={closure.length}"
  logInfo "PRIMAL80_CANONICAL_AUDIT_PASS roots=15 edges=12"
