/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyPopulation
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
open Lean Elab Command
open RH080Next.Explicit RH080Next.AnalyticFlatFamily Real MeasureTheory

example (m:ℕ)(hm:0<m)(t:ℝ) :
    sin (Real.pi*t)*poly m t=sin ((2*(m:ℝ)-1)*Real.pi*t) := sin_mul_poly m hm t
example (m:ℕ)(hm:0<m) :
    (∫t in (0:ℝ)..1,|poly m t|)≤2/Real.pi*(1+Real.log (4*(m:ℝ)-2)) := periodic_norm_bound m hm
example (m:ℕ)(hm:0<m) : nodalF0 (nodes m) m=(2*(m:ℝ)-1)/(m:ℝ) := normalization m hm
example (m:ℕ)(hm:0<m) :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum (nodes m) m)=0 := leakage_zero m hm
example (m:ℕ)(hm:0<m) :
    IEANTN.CMSFunctional.Eligible (inverseCosine (affineSpectrum (nodes m) m))
      (affineSpectrum (nodes m) m) := actual_eligible m hm
example (hNorm:SourceBRFourierNormFive)(hUniform:SourceBRUniformPopulationQ1)
    (hRH:RiemannHypothesis)(m:ℕ)(hm:0<m)(α ε:ℝ)(hα:0≤α)(hε:0<ε) :
    IEANTN.CMSFunctional.GoodCoefficient α
      ((2*(m:ℝ)/(2*(m:ℝ)-1))*(α+(1+Real.log (4*(m:ℝ)-2))/Real.pi)+ε) :=
  actual_population_curve hNorm hUniform hRH m hm α ε hα hε
example (hNorm:SourceBRFourierNormFive)(hUniform:SourceBRUniformPopulationQ1)
    (hRH:RiemannHypothesis)(m:ℕ)(hm:0<m)(α:ℝ)(hα:0≤α) :
    (IEANTN.CMSFunctional.goodCoefficients α).Nonempty ∧
      sInf (IEANTN.CMSFunctional.goodCoefficients α)≤
      (2*(m:ℝ)/(2*(m:ℝ)-1))*(α+(1+Real.log (4*(m:ℝ)-2))/Real.pi) :=
  actual_population_infimum hNorm hUniform hRH m hm α hα

private def proofValue? : ConstantInfo→Option Expr
  | .thmInfo i=>some i.value
  | .defnInfo i=>some i.value
  | _=>none
private partial def proofClosure (env:Environment)(pending:List Name)(seen:NameSet:={}) : NameSet :=
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
  let roots:=#[`RH080Next.AnalyticFlatFamily.order_ge_one,
    `RH080Next.AnalyticFlatFamily.sin_mul_poly,
    `RH080Next.AnalyticFlatFamily.poly_abs_le,
    `RH080Next.AnalyticFlatFamily.poly_abs_le_csc,
    `RH080Next.AnalyticFlatFamily.periodic_norm_eq_twice_half,
    `RH080Next.AnalyticFlatFamily.integral_csc_cut_half,
    `RH080Next.AnalyticFlatFamily.periodic_norm_bound,
    `RH080Next.AnalyticFlatFamily.nodes_length,`RH080Next.AnalyticFlatFamily.node_eq,
    `RH080Next.AnalyticFlatFamily.polynomial_identity,
    `RH080Next.AnalyticFlatFamily.normalization,
    `RH080Next.AnalyticFlatFamily.actual_F0,
    `RH080Next.AnalyticFlatFamily.window_bound,
    `RH080Next.AnalyticFlatFamily.attained_maximum,
    `RH080Next.AnalyticFlatFamily.leakage_zero,
    `RH080Next.AnalyticFlatFamily.denominator,
    `RH080Next.AnalyticFlatFamily.actual_eligible,
    `RH080Next.AnalyticFlatFamily.actual_norm_le,
    `RH080Next.AnalyticFlatFamily.width_positive,
    `RH080Next.AnalyticFlatFamily.width_mass_identity,
    `RH080Next.AnalyticFlatFamily.actual_population_curve,
    `RH080Next.AnalyticFlatFamily.actual_population_infimum]
  for root in roots do
    let some (.thmInfo _) :=env.find? root | throwError "Missing flat-family theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected flat-family axiom {root}: {axioms}"
    logInfo m!"FLAT_FAMILY_AXIOMS {root}: {axioms}"
  let used:=proofClosure env [`RH080Next.AnalyticFlatFamily.actual_population_infimum]
  for required in #[`RH080Next.AnalyticFlatFamily.actual_population_curve,
    `RH080Next.AnalyticFlatFamily.periodic_norm_bound,
    `RH080Next.AnalyticFlatFamily.sin_mul_poly,
    `RH080Next.AnalyticFlatFamily.poly_abs_le_csc,
    `RH080Next.AnalyticFlatFamily.integral_csc_cut_half,
    `RH080Next.AnalyticFlat64.cscPrimitive_hasDerivAt,
    `RH080Next.AnalyticFlatFamily.polynomial_identity,
    `RH080Next.AnalyticFlatFamily.actual_F0,`RH080Next.AnalyticFlatFamily.leakage_zero,
    `RH080Next.Explicit.source_BR_population_goodCoefficient,
    `RH080Next.Explicit.brQ1Error_tendsto_zero] do
    unless used.contains required do throwError "Flat-family actual ANT missing proof {required}"
  for name in used.toList do
    if name.toString.startsWith "Lean.ofReduceBool" || name.toString.startsWith "Lean.trustCompiler" then
      throwError "Native execution dependency {name}"
  let eligible:=proofClosure env [`RH080Next.AnalyticFlatFamily.actual_eligible]
  unless eligible.contains `RH080Next.Explicit.fourier_affine_inverse_eq_window do
    throwError "Generic actual true Fourier eligibility missing"
  logInfo m!"FLAT_FAMILY_AUDIT_PASS roots={roots.size} actual_population_closure={used.toList.length} Std3 forall-m>=1 forall-alpha>=0 forall-epsilon>0 exact5m+1nodes J0 F0=(2m-1)/m M1 actual-Fourier-eligible elementary-integral norm q1-RH actual-pi strict-eventual nonempty-inf-bound NO-endpoint-attainment kernel-only-analytic NOT-PV"
