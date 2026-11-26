/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFullRangeApplications
import ExplicitW4Population
import Lean

set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | _ => none
private partial def proofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n::rest => if seen.contains n then proofClosure env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | some info => match proofValue? info with
      | some body => proofClosure env (body.getUsedConstants.toList++rest) seen
      | none => proofClosure env rest seen
    | none => proofClosure env rest seen
private partial def leadingUses : Expr → List (String×Bool)
  | .lam n _ body _ => (n.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

/- This command audits theorem constants and actual proof edges; it does not
supply mathematical premises. In particular the still-open norm argument
must genuinely be used and is explicitly retained in every theorem type. -/
run_cmd do
  let env ← getEnv
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let finals := #[(`RH080Next.ExplicitProfiles.fap_08_full_of_norm,`RH080Next.FapPV),
    (`RH080Next.ExplicitProfiles.fap_074_full_of_norm,`RH080Next.FapPV),
    (`RH080Next.ExplicitProfiles.fap_075_full_of_norm,`RH080Next.FapPV),
    (`RH080Next.ExplicitProfiles.w4_global_full_of_norm,`RH080Next.WindowPV),
    (`RH080Next.ExplicitProfiles.w4_recorded_population_of_norm,`RH080Next.WindowPV)]
  for (root,ns) in finals do
    let some info@(.thmInfo _) := env.find? root | throwError "Missing final theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified transitive axiom {root}: {axioms}"
    logInfo m!"ORIGINAL_FINAL_AXIOMS {root}: {axioms}"
    logInfo m!"ORIGINAL_FINAL_STATEMENT {root}: {info.type}"
    let some body := proofValue? info | throwError "Missing theorem proof {root}"
    for input in #["hBR","hCMS","hDigamma","hZero","hCount","hEta","hMV","hRH","hNorm"] do
      unless (leadingUses body).any (fun x => x.1==input && x.2) do
        throwError "Unused analytic/numerical input {root}:{input}"
    let closure := proofClosure env [root]
    for child in #[ns++`actual_source_syntax,ns++`actual_main_output,
        ns++`source_output_finite_specification,ns++`source_first_nodal_boundaries,
        ns++`source_first_positive_leak,ns++`source_first_variation,
        `RH080Next.Explicit.source_RH_affine_mellin_identity,
        `RH080Next.Explicit.affine_zero_estimate,
        `RH080Next.Explicit.affine_CMSZeroAdmissible,
        `RH080Next.Primal.actual_full_arithmetic_wing_bound,
        `RH080Next.Primal.actual_nonprimeMangoldt_window_bound,
        `RH080Next.Primal.actual_two_prime_wings_le,
        `RH080Next.Explicit.finite_atomic_continuous_BV_bound,
        `RH080Next.Explicit.mv_interval_entrance_bound,
        `RH080Next.Explicit.cms_zero_count_root_exists] do
      unless closure.contains child do throwError "Missing source/mathematical proof edge {root}->{child}"
    if root==`RH080Next.ExplicitProfiles.w4_recorded_population_of_norm then
      for child in #[ns++`source_first_window_bound,ns++`Execution.actual_maximum_numerator,
          `RH080Next.Explicit.actual_population_goodCoefficient,
          `RH080Next.Explicit.normalized_population_exp,
          `RH080Next.Explicit.eventual_actual_central_normalized_lower,
          `RH080Next.Explicit.eventual_primepower_allowance_tendsto_zero] do
        unless closure.contains child do throwError "Missing population/source proof edge {root}->{child}"
    else
      for child in #[`RH080Next.Explicit.actual_prime_interval_of_residual,
          `RH080Next.Explicit.explicit_budget_assembly,
          `RH080Next.Explicit.strict_prime_of_central_lower,
          `RH080Next.Explicit.strict_prime_of_two_halfopen,
          `RH080Next.FiniteGap.historical_gap_implies_074] do
        unless closure.contains child do throwError "Missing full-range proof edge {root}->{child}"
      unless (leadingUses body).any (fun x => x.1=="hgap" && x.2) do
        throwError "Historical finite source input unused {root}"
  logInfo "ORIGINAL_FINAL_TRUST_AUDIT_PASS roots=5 actual-scalar-source-and-complete-analytic-consumers-used unresolved-FFT-norm-explicit Std3"
