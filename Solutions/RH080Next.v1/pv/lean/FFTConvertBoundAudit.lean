/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundSource
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
    let seen:=seen.insert n
    match env.find? n with
    | some info => match proofValue? info with
      | some body => proofClosure env (body.getUsedConstants.toList++rest) seen
      | none => proofClosure env rest seen
    | none => proofClosure env rest seen
run_cmd do
  let env ← getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[`RH080Next.FFTPV.ConvertBoundSource.actual_body,
    `RH080Next.FFTPV.ConvertBoundSource.condition_eval,
    `RH080Next.FFTPV.ConvertBoundSource.test_eval,
    `RH080Next.FFTPV.ConvertBoundSource.initialize_parameters,
    `RH080Next.FFTPV.ConvertBoundSource.body_execution,
    `RH080Next.FFTPV.ConvertBoundSource.loop_execution,
    `RH080Next.FFTPV.ConvertBoundSource.loop_frame,
    `RH080Next.FFTPV.ConvertBoundSource.lower_eval,
    `RH080Next.FFTPV.ConvertBoundSource.convert_bound_call,
    `RH080Next.FFTPV.ConvertBoundSource.returned_call_unique,
    `RH080Next.FFTPV.ConvertBoundSource.converted_magnitude,
    `RH080Next.FFTPV.ConvertBoundSource.source_convert_bound_total]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source conversion helper theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified conversion helper axiom {root}: {axioms}"
    logInfo m!"FFT_CONVERT_BOUND_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.ConvertBoundSource.source_convert_bound_total]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.ConvertBoundSource.actual_body,
      `RH080Next.FFTPV.ConvertBoundSource.initialize_parameters,
      `RH080Next.FFTPV.ConvertBoundSource.loop_execution,
      `RH080Next.FFTPV.ConvertBoundSource.loop_frame,
      `RH080Next.FFTPV.ConvertBoundSource.lower_eval,
      `RH080Next.FFTPV.ConvertBoundSource.result_fits,
      `RH080Next.FFTPV.ConvertBoundSource.converted_magnitude,
      `RH080Next.FFTPV.ConvertBoundSource.returned_call_unique] do
    unless dependencies.contains child do throwError "Missing actual source/conversion link {child}"
  logInfo m!"FFT_CONVERT_BOUND_AUDIT_PASS roots=12 closure={dependencies.toList.length} actual-character-syntax-both-profiles real-parameters-and-local-birth full-sentinel-loop unsigned-no-wrap exact-six-limb-magnitude read-only-array-and-caller all-permitted-Calls no-native no-sorry HELPER_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
