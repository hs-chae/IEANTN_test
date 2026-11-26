/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlat64Population
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
open Lean Elab Command
open RH080Next.Explicit RH080Next.AnalyticFlat64 Real MeasureTheory

example (t:ℝ) : sin (Real.pi*t)*poly t=sin (127*Real.pi*t) := sin_mul_poly t
example : (∫t in (0:ℝ)..1,|poly t|)≤2/Real.pi*(1+log 254) := periodic_norm_bound
example : nodalF0 nodes 64=(127:ℝ)/64 := normalization
example : IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes 64)=0 := leakage_zero
example : ∀v:ℝ,|affineSpectrum nodes 64 v|≤1 := window_bound
example : IEANTN.CMSFunctional.Eligible (inverseCosine (affineSpectrum nodes 64))
    (affineSpectrum nodes 64) := actual_eligible
example (hNorm:SourceBRFourierNormFive)(hUniform:SourceBRUniformPopulationQ1)
    (hRH:RiemannHypothesis)(α:ℝ)(hα:0≤α) :
    IEANTN.CMSFunctional.GoodCoefficient α ((21/10:ℝ)+(128/127:ℝ)*α) :=
  actual_population_curve hNorm hUniform hRH α hα
example (hNorm:SourceBRFourierNormFive)(hUniform:SourceBRUniformPopulationQ1)
    (hRH:RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 40 ((53867:ℝ)/1270) := by
  exact actual_population_forty hNorm hUniform hRH

private def proofValue? : ConstantInfo→Option Expr
  | .thmInfo i=>some i.value
  | .defnInfo i=>some i.value
  | _=>none
private partial def proofClosure (env:Environment) (pending:List Name) (seen:NameSet:={}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then proofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match proofValue? info with
      | some body=>proofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>proofClosure env rest seen
    | none=>proofClosure env rest seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[`RH080Next.AnalyticFlat64.sin_mul_poly,
    `RH080Next.AnalyticFlat64.poly_abs_le,`RH080Next.AnalyticFlat64.poly_abs_le_csc,
    `RH080Next.AnalyticFlat64.periodic_norm_eq_twice_half,
    `RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt,
    `RH080Next.AnalyticFlat64.integral_csc_cut_half,
    `RH080Next.AnalyticFlat64.periodic_norm_bound,
    `RH080Next.AnalyticFlat64.log254_lt,`RH080Next.AnalyticFlat64.polynomial_identity,
    `RH080Next.AnalyticFlat64.actual_F0,`RH080Next.AnalyticFlat64.window_bound,
    `RH080Next.AnalyticFlat64.attained_maximum,`RH080Next.AnalyticFlat64.leakage_zero,
    `RH080Next.AnalyticFlat64.denominator,`RH080Next.AnalyticFlat64.actual_eligible,
    `RH080Next.AnalyticFlat64.analytic_intercept_strict,
    `RH080Next.AnalyticFlat64.actual_norm_strict,
    `RH080Next.AnalyticFlat64.actual_population_curve,
    `RH080Next.AnalyticFlat64.actual_population_eventual,
    `RH080Next.AnalyticFlat64.actual_population_forty,
    `RH080Next.AnalyticFlat64.improves_previous_flat]
  for root in roots do
    let some (.thmInfo _) :=env.find? root | throwError "Missing flat64 theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected flat64 axiom {root}: {axioms}"
    logInfo m!"FLAT64_AXIOMS {root}: {axioms}"
  let used:=proofClosure env [`RH080Next.AnalyticFlat64.actual_population_curve]
  for required in #[`RH080Next.AnalyticFlat64.periodic_norm_bound,
    `RH080Next.AnalyticFlat64.sin_mul_poly,`RH080Next.AnalyticFlat64.poly_abs_le_csc,
    `RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt,
    `RH080Next.AnalyticFlat64.integral_csc_cut_half,`RH080Next.AnalyticFlat64.log254_lt,
    `RH080Next.AnalyticFlat64.polynomial_identity,`RH080Next.AnalyticFlat64.actual_F0,
    `RH080Next.AnalyticFlat64.leakage_zero,
    `RH080Next.Explicit.source_BR_population_goodCoefficient,
    `RH080Next.Explicit.brQ1Error_tendsto_zero] do
    unless used.contains required do throwError "Flat64 actual ANT missing consumed proof {required}"
  for name in used.toList do
    if name.toString.startsWith "Lean.ofReduceBool" || name.toString.startsWith "Lean.trustCompiler" then
      throwError "Native execution dependency {name}"
  let eligible:=proofClosure env [`RH080Next.AnalyticFlat64.actual_eligible]
  unless eligible.contains `RH080Next.Explicit.fourier_affine_inverse_eq_window do
    throwError "Flat64 actual true Fourier eligibility missing"
  logInfo m!"FLAT64_AUDIT_PASS roots={roots.size} actual_population_closure={used.toList.length} Std3 exact321nodes m64 J0 F0=127/64 M1 actual-Fourier eligible elementary-integral norm q1-RH actual-pi strict-eventual kernel-only-analytic NOT-PV"
