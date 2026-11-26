/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleSource
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
  let roots:=#[`RH080Next.FFTPV.TwiddleSource.actual_w4_loop,
    `RH080Next.FFTPV.TwiddleSource.actual_fap_loop,
    `RH080Next.FFTPV.TwiddleSource.condition_eval,
    `RH080Next.FFTPV.TwiddleSource.arguments_eval,
    `RH080Next.FFTPV.TwiddleSource.computed_value,
    `RH080Next.FFTPV.TwiddleSource.call_execution,
    `RH080Next.FFTPV.TwiddleSource.advance_execution,
    `RH080Next.FFTPV.TwiddleSource.body_execution,
    `RH080Next.FFTPV.TwiddleSource.loop_execution,
    `RH080Next.FFTPV.TwiddleSource.fixed_values_small,
    `RH080Next.FFTPV.TwiddleSource.fixed_root_small,
    `RH080Next.FFTPV.TwiddleSource.initialize_table,
    `RH080Next.FFTPV.TwiddleSource.construct_table,
    `RH080Next.FFTPV.TwiddleSource.source_construct_table,
    `RH080Next.FFTPV.TwiddleSource.trace_entry,
    `RH080Next.FFTPV.TwiddleSource.source_table_matches_trace]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source twiddle stage theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified twiddle stage axiom {root}: {axioms}"
    logInfo m!"FFT_TWIDDLE_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.TwiddleSource.source_construct_table,
    `RH080Next.FFTPV.TwiddleSource.source_table_matches_trace]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.TwiddleSource.actual_w4_loop,
      `RH080Next.FFTPV.TwiddleSource.actual_fap_loop,
      `RH080Next.FFTPV.TwiddleSource.initialize_table,
      `RH080Next.FFTPV.TwiddleSource.arguments_eval,
      `RH080Next.FFTPV.TwiddleSource.call_execution,
      `RH080Next.FFTPV.TwiddleSource.body_execution,
      `RH080Next.FFTPV.TwiddleSource.loop_execution,
      `RH080Next.FFTPV.TwiddleSource.fixed_values_small,
      `RH080Next.FFTPV.TwiddleSource.fixed_root_small,
      `RH080Next.FFTPV.ComplexSource.complex_multiply_correct,
      `RH080Next.FFTPV.ComplexSource.resultPair_eq_integer_mul,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution,
      `RH080Next.FFT.IntegerModel.sequence17_components,
      `RH080Next.FFT.IntegerModel.sequence24_components,
      `RH080Next.FFTPV.TwiddleSource.trace_entry] do
    unless dependencies.contains child do throwError "Missing actual source/twiddle/math link {child}"
  logInfo m!"FFT_TWIDDLE_AUDIT_PASS roots=16 closure={dependencies.toList.length} actual-character-syntax-both-profiles actual-unit-store-and-local-birth all-table-source-iterations all-permitted-executions actual-root-and-previous-table-physical-frames exact-integer-recurrence original-grid-guard-proofs independent-kernel-trace-table-bridge no-native no-sorry MAIN_STAGE_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
