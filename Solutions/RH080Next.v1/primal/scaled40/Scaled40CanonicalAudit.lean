/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Scaled40WitnessSolution
import Scaled40AsymptoticSolution
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
    if !(root.toString.startsWith "RHOnePrime." || root.toString.startsWith "RH080." || root.toString.startsWith "RH080Next." ||
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

example : CMSFunctionalInput.v1.gap_reduction = SourceCMSFunctional := rfl
example : CMSFunctionalInput.v1.population_reduction = SourceCMSPopulation := rfl
example : RH.v1.hypothesis = RiemannHypothesis := rfl

example : GaussianFourierWitness.v4.integral_fourier_witness :=
  GaussianFourierWitness.v4.challenge_integral_fourier_witness
example : GaussianFourierWitness.v4.objective_witness :=
  RH080Next.Scaled40Canonical.actual_objective_witness
example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis →
    EventualGapBound (20582561296/24680948495 : ℝ) :=
  RH080Next.Scaled40Canonical.actual_normalized_gap
example : CMSFunctionalInput.v1.population_reduction → RH.v1.hypothesis →
    RHAsymptoticGaussian.v4.population_curve := RH080Next.Scaled40Canonical.actual_population_curve
example : CMSFunctionalInput.v1.population_reduction → RH.v1.hypothesis →
    RHAsymptoticGaussian.v4.population_count := RH080Next.Scaled40Canonical.actual_population_count
example : GaussianFourierWitness.v4.integral_fourier_witness =
    (∃ F G : ℝ → ℝ, Eligible F G ∧ mass F ≤ (7484567744/10000000000 : ℝ) ∧
      positiveLeak G ≤ (313227945/10000000000 : ℝ) ∧
      (1 : ℝ) ≤ F 0) := rfl

run_cmd do
  let env ← getEnv
  let roots := #[
    `GaussianFourierWitness.v4.challenge_integral_fourier_witness,
    `GaussianFourierWitness.v4.challenge_objective_witness,
    `RHAsymptoticGaussian.v4.challenge_normalized_gap,
    `RHAsymptoticGaussian.v4.challenge_gap_below_readable,
    `RHAsymptoticGaussian.v4.challenge_gap_below_v3,
    `RHAsymptoticGaussian.v4.challenge_gap_below_v2,
    `RHAsymptoticGaussian.v4.challenge_gap_below_v1,
    `RHAsymptoticGaussian.v4.challenge_gap_below_printed_2026,
    `RHAsymptoticGaussian.v4.challenge_population_curve,
    `RHAsymptoticGaussian.v4.challenge_population_count,
    `RH080Next.Scaled40Canonical.actual_objective_witness,
    `RH080Next.Scaled40Canonical.actual_normalized_gap,
    `RH080Next.Scaled40Canonical.actual_gap_below_readable,
    `RH080Next.Scaled40Canonical.actual_gap_below_v3,
    `RH080Next.Scaled40Canonical.actual_gap_below_v2,
    `RH080Next.Scaled40Canonical.actual_gap_below_v1,
    `RH080Next.Scaled40Canonical.actual_gap_below_printed_2026,
    `RH080Next.Scaled40Canonical.actual_population_curve,
    `RH080Next.Scaled40Canonical.actual_population_count]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted axiom {root}: {axioms}"
    logInfo m!"SCALED40_V4_CANONICAL_AXIOMS {root}: {axioms}"
    if root == `GaussianFourierWitness.v4.challenge_objective_witness then
      unless (leadingUses info.value).any (fun p => p.1=="hNumeric" && p.2) do
        throwError "Raw integral witness not consumed"
    if root == `RHAsymptoticGaussian.v4.challenge_normalized_gap ||
      root == `RHAsymptoticGaussian.v4.challenge_population_curve then
      for parameter in ["hCMS","rh","hNumeric"] do
        unless (leadingUses info.value).any (fun p => p.1==parameter && p.2) do
          throwError "Source/numerical input not consumed {root}:{parameter}"
  let edges := #[
    (`GaussianFourierWitness.v4.challenge_integral_fourier_witness,`RH080Next.Scaled40.eligible),
    (`GaussianFourierWitness.v4.challenge_integral_fourier_witness,`RH080Next.Scaled40.physical_norm_upper),
    (`GaussianFourierWitness.v4.challenge_integral_fourier_witness,`RH080Next.Scaled40.physical_full_wings_upper),
    (`GaussianFourierWitness.v4.challenge_integral_fourier_witness,`RH080Next.Scaled40.physicalF_zero_exact),
    (`RH080Next.Scaled40.eligible,`RH080Next.Scaled40Fourier.fourier_scaled_physical),
    (`RHAsymptoticGaussian.v4.challenge_normalized_gap,`RHOnePrime.CMSFunctional.gap_from_functional),
    (`RHAsymptoticGaussian.v4.challenge_population_curve,`RHOnePrime.CMSFunctional.population_from_functional),
    (`RHAsymptoticGaussian.v4.challenge_population_count,`RHOnePrime.CMSFunctional.eventual_count_of_good),
    (`RH080Next.Scaled40Canonical.actual_objective_witness,`GaussianFourierWitness.v4.challenge_integral_fourier_witness),
    (`RH080Next.Scaled40Canonical.actual_objective_witness,`GaussianFourierWitness.v4.challenge_objective_witness),
    (`RH080Next.Scaled40Canonical.actual_normalized_gap,`RH080Next.Scaled40Canonical.actual_objective_witness),
    (`RH080Next.Scaled40Canonical.actual_population_curve,`RH080Next.Scaled40Canonical.actual_objective_witness)]
  for (root,dependency) in edges do
    let some (.thmInfo info) := env.find? root | throwError "Missing root {root}"
    unless info.value.getUsedConstants.contains dependency do
      throwError "Actual proof edge missing {root}->{dependency}"
  let closure := applicationClosure env roots.toList []
  for old in #[`RH080.Gaussian28.normSource,`RH080.Gaussian28.wingSource,
    `RH080.Primal56Fourier.fourier_actual_physical,
    `GaussianFourierWitness.v3.challenge_integral_fourier_witness,`RH080.Gaussian40.normSource,`RH080.Gaussian40.wingSource,
    `RH080.Gaussian40.physicalF,`RH080.Gaussian40.physicalG,
    `RH080.Primal80Fourier.fourier_actual_physical,
    `GaussianFourierWitness.v2.challenge_integral_fourier_witness,
    `RHOnePrime.GaussianKernel.normSource,`RHOnePrime.GaussianKernel.wingSource,
    `RHOnePrime.GaussianKernel.physicalF,`RHOnePrime.GaussianKernel.physicalG,
    `RHOnePrime.GaussianFourier.actual_even_transform,
    `RHOnePrime.GaussianFourier.fourier_actual_physical,
    `GaussianFourierWitness.v1.challenge_integral_fourier_witness] do
    if closure.contains old then throwError "Old actual witness consumed {old}"
  for required in #[`RH080Next.Scaled40.normSource,`RH080Next.Scaled40.wingSource,
    `RH080Next.Scaled40Fourier.fourier_scaled_physical,
    `RH080Next.Scaled40.physical_norm_upper,`RH080Next.Scaled40.physical_full_wings_upper] do
    unless closure.contains required do throwError "Required actual new provider absent {required}"
  logInfo m!"SCALED40_V4_COMPLETE_NEW_SOURCE_CLOSURE_PASS visited={closure.length}"
  logInfo "SCALED40_V4_CANONICAL_AUDIT_PASS roots=19 edges=12"
