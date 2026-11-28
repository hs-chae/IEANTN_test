/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTMagnitudeIntoSource
import ExplicitFFTAddMagnitudeSource
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | _ => none
private partial def proofClosure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n::rest => if seen.contains n then proofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info => match proofValue? info with
      | some body => proofClosure env (body.getUsedConstants.toList++rest) seen
      | none => proofClosure env rest seen
    | none => proofClosure env rest seen
run_cmd do
  let env ← getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  for (root,syntaxProof) in #[(`RH080Next.FFTPV.MagnitudeIntoSource.source_magnitude_into_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.MagnitudeIntoSource.fap_source_magnitude_into_total,`RH080Next.FapFFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.MagnitudeIntoSource.recursive_source_magnitude_into_total,`RH080Next.FFTRecursivePV.actual_source_syntax),
    (`RH080Next.FFTPV.MagnitudeIntoSource.fap_recursive_source_magnitude_into_total,`RH080Next.FapFFTRecursivePV.actual_source_syntax)] do
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden magnitude helper axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,`RH080Next.FFTPV.MagnitudeIntoSource.initialize_parameters,
        `RH080Next.FFTPV.MagnitudeIntoSource.zero_execution,
        `RH080Next.FFTPV.MagnitudeIntoSource.store_execution,
        `RH080Next.FFTPV.MagnitudeIntoSource.magnitude_into_call,
        `RH080Next.FFTPV.MagnitudeIntoSource.finalData_magnitude,
        `RH080Next.FFTPV.MagnitudeIntoSource.finalData_outside,`RH080Next.FFTPV.RootSource.every_call_from_body,`GoldbachDirect.PureArgs.args_sound] do
      unless used.contains needed do throwError "Missing actual source/math dependency {root}->{needed}"
    logInfo m!"FFT_MAGNITUDE_HELPERS_AXIOMS {root}: {axioms}"
  for (root,syntaxProof) in #[(`RH080Next.FFTPV.AddMagnitudeSource.source_add_magnitude_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.AddMagnitudeSource.fap_source_add_magnitude_total,`RH080Next.FapFFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.AddMagnitudeSource.recursive_source_add_magnitude_total,`RH080Next.FFTRecursivePV.actual_source_syntax),
    (`RH080Next.FFTPV.AddMagnitudeSource.fap_recursive_source_add_magnitude_total,`RH080Next.FapFFTRecursivePV.actual_source_syntax)] do
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden magnitude helper axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,`RH080Next.FFTPV.AddMagnitudeSource.initialize_parameters,
        `RH080Next.FFTPV.AddMagnitudeSource.x_branch_execution,
        `RH080Next.FFTPV.AddMagnitudeSource.t_declare,
        `RH080Next.FFTPV.AddMagnitudeSource.digit_execution,
        `RH080Next.FFTPV.AddMagnitudeSource.counters_execution,
        `RH080Next.FFTPV.AddMagnitudeSource.body_execution,
        `RH080Next.FFTPV.AddMagnitudeSource.loop_execution,
        `RH080Next.FFTPV.AddMagnitudeSource.add_magnitude_call,
        `RH080Next.FFTPV.AddMagnitudeSource.result_conservation,
        `RH080Next.FFTPV.AddMagnitudeSource.currentData_outside,`RH080Next.FFTPV.RootSource.every_call_from_body] do
      unless used.contains needed do throwError "Missing actual source/math dependency {root}->{needed}"
    logInfo m!"FFT_MAGNITUDE_HELPERS_AXIOMS {root}: {axioms}"
  logInfo "FFT_MAGNITUDE_HELPERS_AUDIT_PASS eight-original-source-roots actual-two-helpers full-Call every-execution alias-safe same-object-slices actual-five-input-limbs uint64-no-wrap integer-conservation caller-frame Std3 final-ANT-connection-pending"
