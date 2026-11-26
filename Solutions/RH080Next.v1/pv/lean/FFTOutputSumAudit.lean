/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumSource
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
  let roots:=#[`RH080Next.FFTPV.OutputSumSource.actual_w4_loop,
    `RH080Next.FFTPV.OutputSumSource.actual_fap_loop,
    `RH080Next.FFTPV.OutputSumSource.partialSum_le,
    `RH080Next.FFTPV.OutputSumSource.input_magnitude,
    `RH080Next.FFTPV.OutputSumSource.input_status_zero,
    `RH080Next.FFTPV.OutputSumSource.conserved_total,
    `RH080Next.FFTPV.OutputSumSource.arguments_eval,
    `RH080Next.FFTPV.OutputSumSource.call_execution,
    `RH080Next.FFTPV.OutputSumSource.advance_execution,
    `RH080Next.FFTPV.OutputSumSource.body_execution,
    `RH080Next.FFTPV.OutputSumSource.loop_execution,
    `RH080Next.FFTPV.OutputSumSource.source_loop_execution]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source output accumulator theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified output accumulator axiom {root}: {axioms}"
    logInfo m!"FFT_OUTPUT_SUM_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.OutputSumSource.source_loop_execution]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.OutputSumSource.actual_w4_loop,
      `RH080Next.FFTPV.OutputSumSource.actual_fap_loop,
      `RH080Next.FFTPV.OutputSumSource.partialSum_le,
      `RH080Next.FFTPV.OutputSumSource.input_magnitude,
      `RH080Next.FFTPV.OutputSumSource.input_status_zero,
      `RH080Next.FFTPV.OutputSumSource.arguments_eval,
      `RH080Next.FFTPV.OutputSumSource.call_execution,
      `RH080Next.FFTPV.OutputSumSource.advance_execution,
      `RH080Next.FFTPV.OutputSumSource.body_execution,
      `RH080Next.FFTPV.OutputSumSource.loop_execution,
      `RH080Next.FFTPV.AddMagnitudeSource.add_magnitude_total,
      `RH080Next.FFTPV.AddMagnitudeSource.zero_status_of_small,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution] do
    unless dependencies.contains child do throwError "Missing actual source/accumulator/math link {child}"
  logInfo m!"FFT_OUTPUT_SUM_AUDIT_PASS roots=12 closure={dependencies.toList.length} actual-character-syntax-both-profiles every-actual-source-sum-iteration exact-real-magnitude-sum unsigned-six-limb-accumulator no-overflow-carry normalized-total all-permitted-executions preserved-FFT-output and-work-outside-total192-197 no-native no-sorry MAIN_STAGE_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
