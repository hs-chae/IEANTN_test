/- Focused append audit: the canonical mathematical nodes consume the accepted
complete source-first program result. No generic platform success is assumed. -/
import DualNetworkIntegration
import Lean

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command

namespace RH080PV.Canonical

theorem actual_ratio_floor : CMSFunctionalObstruction.v1.ratio_floor :=
  CMSFunctionalObstruction.v1.challenge_ratio_floor
    CMSDualCertificate.v1.challenge_integral_witness

theorem actual_exclusion : CMSFunctionalObstruction.v1.excludes_four_fifths :=
  CMSFunctionalObstruction.v1.challenge_excludes_four_fifths actual_ratio_floor

theorem actual_network_result : RH080PV.Verified.SourceFirstOutput ∧
    CMSDualCertificate.v1.integral_witness ∧ CMSFunctionalObstruction.v1.ratio_floor ∧
    CMSFunctionalObstruction.v1.excludes_four_fifths :=
  ⟨RH080.Dual.source_integral_witness_with_source.1,
   CMSDualCertificate.v1.challenge_integral_witness, actual_ratio_floor, actual_exclusion⟩

end RH080PV.Canonical

private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | _ => none

private partial def valueClosure (env : Environment) (queue : List Name)
    (visited : NameSet := {}) : NameSet :=
  match queue with
  | [] => visited
  | name::rest =>
    if visited.contains name then valueClosure env rest visited
    else
      let visited := visited.insert name
      match env.find? name with
      | some info =>
        match proofValue? info with
        | some value => valueClosure env (value.getUsedConstants.toList ++ rest) visited
        | none => valueClosure env rest visited
      | none => valueClosure env rest visited

private partial def leadingUses : Expr → List (String × Bool)
  | .lam name _ body _ => (name.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let roots := #[`RH080.Dual.source_integral_witness_with_source,
    `CMSDualCertificate.v1.challenge_integral_witness,
    `CMSFunctionalObstruction.v1.challenge_ratio_floor,
    `CMSFunctionalObstruction.v1.challenge_excludes_four_fifths,
    `RH080PV.Canonical.actual_ratio_floor,`RH080PV.Canonical.actual_exclusion,
    `RH080PV.Canonical.actual_network_result]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing canonical theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden canonical axiom {root}: {axioms}"
    logInfo m!"PV_CANONICAL_AXIOMS {root}: {axioms}"
  for root in #[`RH080PV.Canonical.actual_ratio_floor,`RH080PV.Canonical.actual_exclusion,
      `RH080PV.Canonical.actual_network_result] do
    let closure := valueClosure env [root]
    for required in #[`RH080.Dual.actual_source_first_functional_result,
      `RH080PV.actual_source_syntax,`RH080PV.checkedSyntax_sound,
      `RH080PV.Output.actual_host_main,`RH080PV.Execution.actual_numerical_execution,
      `RH080PV.Verified.source_result_controls_grid] do
      unless closure.contains required do throwError "Missing canonical source dependency {root}->{required}"
      logInfo m!"PV_CANONICAL_SOURCE_CONSUMED {root}->{required}"
    for forbidden in #[`RH080PV.Model.sampleBound_all,`RH080.Dual.kernel_compact_global,
      `RH080.Dual.kernel_compact_obstruction] do
      if closure.contains forbidden then throwError "D-only canonical shortcut {root}->{forbidden}"
  for (root,premise) in #[(`CMSFunctionalObstruction.v1.challenge_ratio_floor,"witness"),
      (`CMSFunctionalObstruction.v1.challenge_excludes_four_fifths,"floor")] do
    let some info := env.find? root | throwError "Missing canonical pipeline"
    let some body := proofValue? info | throwError "Missing canonical proof"
    unless (leadingUses body).any (fun item => item.1==premise && item.2) do
      throwError "Canonical input not consumed {root}:{premise}"
  logInfo "PV_CANONICAL_AUDIT_PASS roots=7 closed-source-paths=3 no-native no-sorry no-D-cap-shortcut"
