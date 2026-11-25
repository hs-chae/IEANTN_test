/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Primal80ActualFourier
open Lean Elab Command MeasureTheory
open scoped FourierTransform

private partial def applicationClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root::rest, seen =>
    if seen.contains root then applicationClosure env rest seen else
    let seen := root::seen
    if !(root.toString.startsWith "RHOnePrime." || root.toString.startsWith "RH080.") then
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

example : 𝓕 (fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ)) =
    fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ) :=
  RH080.Primal80Fourier.fourier_actual_physical
example : Integrable RH080.Gaussian40.physicalF := RH080.Primal80Fourier.integrable_physicalF
example : Integrable RH080.Gaussian40.physicalG := RH080.Primal80Fourier.integrable_physicalG
example : Continuous RH080.Gaussian40.physicalF := RH080.Primal80Fourier.continuous_physicalF
example : Continuous RH080.Gaussian40.physicalG := RH080.Primal80Fourier.continuous_physicalG
example : Function.Even RH080.Gaussian40.physicalF := RH080.Primal80Fourier.physicalF_even
example : Function.Even RH080.Gaussian40.physicalG := RH080.Primal80Fourier.physicalG_even

run_cmd do
  let env ← getEnv
  let roots := #[
    `RH080.Primal80Fourier.actual_norm_expansion,
    `RH080.Primal80Fourier.actual_wing_expansion,
    `RH080.Primal80Fourier.actual_even_transform,
    `RH080.Primal80Fourier.actual_source_transform,
    `RH080.Primal80Fourier.fourier_actual_physical,
    `RH080.Primal80Fourier.integrable_complex_physicalF,
    `RH080.Primal80Fourier.integrable_complex_physicalG,
    `RH080.Primal80Fourier.integrable_physicalF,
    `RH080.Primal80Fourier.integrable_physicalG,
    `RH080.Primal80Fourier.continuous_physicalF,
    `RH080.Primal80Fourier.continuous_physicalG,
    `RH080.Primal80Fourier.physicalF_even,
    `RH080.Primal80Fourier.physicalG_even]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted axiom {root}: {axioms}"
    logInfo m!"PRIMAL80_AXIOMS {root}: {axioms}"
  let edges := #[
    (`RH080.Primal80Fourier.fourier_actual_physical,`RHOnePrime.GaussianFourier.fourier_sourceWave),
    (`RH080.Primal80Fourier.fourier_actual_physical,`RH080.Primal80Fourier.actual_source_transform),
    (`RH080.Primal80Fourier.fourier_actual_physical,`RH080.Primal80Fourier.sourceWave_physicalF),
    (`RH080.Primal80Fourier.fourier_actual_physical,`RH080.Primal80Fourier.sourceWave_physicalG),
    (`RH080.Primal80Fourier.actual_source_transform,`RH080.Primal80Fourier.actual_even_transform),
    (`RH080.Primal80Fourier.actual_even_transform,`RHOnePrime.GaussianFourier.coeffPoly_evenTransformCoeffs)]
  for (root,dependency) in edges do
    let some (.thmInfo info) := env.find? root | throwError "Missing root {root}"
    unless info.value.getUsedConstants.contains dependency do
      throwError "Expected actual proof edge missing {root} -> {dependency}"
  let closure := applicationClosure env roots.toList []
  let forbidden := #[
    `RHOnePrime.GaussianKernel.normSource, `RHOnePrime.GaussianKernel.wingSource,
    `RHOnePrime.GaussianKernel.physicalF, `RHOnePrime.GaussianKernel.physicalG,
    `RHOnePrime.GaussianFourier.normEvenSource,
    `RHOnePrime.GaussianFourier.actual_even_transform,
    `RHOnePrime.GaussianFourier.actual_source_transform,
    `RHOnePrime.GaussianFourier.fourier_actual_physical]
  for old in forbidden do
    if closure.contains old then throwError "Old actual witness consumed {old}"
  unless closure.contains `RH080.Gaussian40.normSource &&
      closure.contains `RH080.Gaussian40.wingSource do
    throwError "New exact coefficient sources not consumed"
  logInfo m!"PRIMAL80_NEW_SOURCE_CLOSURE_PASS visited={closure.length}"
  logInfo "PRIMAL80_FOURIER_AUDIT_PASS roots=13 edges=6"
