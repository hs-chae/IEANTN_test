/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyAsymptoticPopulation
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Lean Elab Command Real Filter RH080Next.Explicit
open scoped Topology
open RH080Next.AnalyticFlatFamilyAsymptotic

example : Tendsto
    (fun α : ℝ => RH080Next.AnalyticFlatFamily.width (mesh α) α-α-Real.log α/Real.pi)
    atTop (𝓝 ((2+Real.log (2*Real.pi))/Real.pi)) := width_offset_tendsto
example (hNorm : SourceBRFourierNormFive) (hUniform : SourceBRUniformPopulationQ1)
    (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0<η → ∀ᶠ α : ℝ in atTop,
      IEANTN.CMSFunctional.GoodCoefficient α
        (α+Real.log α/Real.pi+(2+Real.log (2*Real.pi))/Real.pi+η) := by
  intro η hη
  exact actual_population_curve hNorm hUniform hRH η hη
example (hNorm : SourceBRFourierNormFive) (hUniform : SourceBRUniformPopulationQ1)
    (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0<η → ∀ᶠ α : ℝ in atTop,
      (IEANTN.CMSFunctional.goodCoefficients α).Nonempty ∧
      sInf (IEANTN.CMSFunctional.goodCoefficients α)≤
        α+Real.log α/Real.pi+(2+Real.log (2*Real.pi))/Real.pi+η := by
  intro η hη
  exact actual_population_infimum hNorm hUniform hRH η hη
example (hNorm : SourceBRFourierNormFive) (hUniform : SourceBRUniformPopulationQ1)
    (hRH : RiemannHypothesis) :
    ∀ η : ℝ, 0<η → ∀ᶠ α : ℝ in atTop, ∃δ : ℝ,0<δ ∧ ∀ᶠ x : ℝ in atTop,
      (α+δ)*sqrt x≤(IEANTN.CMSFunctional.halfOpenCount
        (α+Real.log α/Real.pi+(2+Real.log (2*Real.pi))/Real.pi+η) x:ℝ) := by
  intro η hη
  exact actual_population_eventual hNorm hUniform hRH η hη

private def proofValue? : ConstantInfo→Option Expr
  | .thmInfo i=>some i.value
  | .defnInfo i=>some i.value
  | .opaqueInfo i=>some i.value
  | _=>none
private partial def proofTypeClosure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then proofTypeClosure env rest seen else
      let seen := seen.insert n
      match env.find? n with
      | none => proofTypeClosure env rest seen
      | some info =>
        let deps := info.type.getUsedConstants.toList
        match proofValue? info with
        | some body => proofTypeClosure env (body.getUsedConstants.toList ++ deps ++ rest) seen
        | none => proofTypeClosure env (deps ++ rest) seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[`RH080Next.AnalyticFlatFamilyAsymptotic.mesh_positive,
    `RH080Next.AnalyticFlatFamilyAsymptotic.radius_positive,
    `RH080Next.AnalyticFlatFamilyAsymptotic.radius_ratio_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.radius_tendsto_atTop,
    `RH080Next.AnalyticFlatFamilyAsymptotic.alpha_div_radius_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.inv_radius_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.log_radius_div_radius_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.log_ratio_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.logarithmic_remainder_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.width_offset_identity,
    `RH080Next.AnalyticFlatFamilyAsymptotic.width_offset_tendsto,
    `RH080Next.AnalyticFlatFamilyAsymptotic.width_eventually_lt,
    `RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_curve,
    `RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_infimum,
    `RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_eventual]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing asymptotic theorem {root}"
    let ax←collectAxioms root
    unless ax.all allowed.contains do throwError "Unexpected asymptotic axiom {root}: {ax}"
    logInfo m!"REAL_ALPHA_ASYMPTOTIC_AXIOMS {root}: {ax}"
  for root in #[`RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_curve,
    `RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_infimum,
    `RH080Next.AnalyticFlatFamilyAsymptotic.actual_population_eventual] do
    let used:=proofTypeClosure env [root]
    for required in #[`RH080Next.AnalyticFlatFamilyAsymptotic.width_offset_tendsto,
      `RH080Next.AnalyticFlatFamilyAsymptotic.radius_ratio_tendsto,
      `RH080Next.AnalyticFlatFamilyAsymptotic.logarithmic_remainder_tendsto,
      `RH080Next.AnalyticFlatFamilyAsymptotic.width_offset_identity,
      `tendsto_nat_floor_mul_div_atTop,
      `RH080Next.AnalyticFlatFamily.actual_population_curve,
      `RH080Next.AnalyticFlatFamily.periodic_norm_bound,
      `RH080Next.Explicit.source_BR_population_goodCoefficient,
      `RH080Next.Explicit.brQ1Error_tendsto_zero,
      `IEANTN.CMSFunctional.piReal,`Nat.primeCounting] do
      unless used.contains required do throwError "Asymptotic actual-ANT dependency missing {root}: {required}"
    for forbidden in #[`IEANTN.CMSFunctional.SourceCMSPopulation,
      `IEANTN.CMSFunctional.SourceCMSFunctional,`sorryAx] do
      if used.contains forbidden then throwError "Extra asymptotic input {root}: {forbidden}"
    for n in used.toList do
      if n.toString.startsWith "Lean.ofReduceBool" || n.toString.startsWith "Lean.trustCompiler" then
        throwError "Native asymptotic leaf {root}: {n}"
    logInfo m!"REAL_ALPHA_ASYMPTOTIC_CLOSURE {root}: {used.toList.length}"
  logInfo m!"REAL_ALPHA_ASYMPTOTIC_AUDIT_PASS roots={roots.size} full-real-alpha rounded-positive-mesh exact-K Std3 actual-GoodCoefficient actual-pi nested-eventual nonempty-infimum no-native no-extra-CMS-source kernel-only-analytic NOT-PV"
