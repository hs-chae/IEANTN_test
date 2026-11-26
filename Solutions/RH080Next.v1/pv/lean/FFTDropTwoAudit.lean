/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoSource
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
  let roots:=#[`RH080Next.FFTPV.DropTwoSource.dropped_magnitude,
    `RH080Next.FFTPV.DropTwoSource.lost_zero_iff_remainder,
    `RH080Next.FFTPV.DropTwoSource.source_eval,
    `RH080Next.FFTPV.DropTwoSource.move_execution,
    `RH080Next.FFTPV.DropTwoSource.step_execution,
    `RH080Next.FFTPV.DropTwoSource.loop_execution,
    `RH080Next.FFTPV.DropTwoSource.clear_execution,
    `RH080Next.FFTPV.DropTwoSource.roundData_magnitude,
    `RH080Next.FFTPV.DropTwoSource.rounding_execution,
    `RH080Next.FFTPV.DropTwoSource.initialize_drop,
    `RH080Next.FFTPV.DropTwoSource.drop_two_total,
    `RH080Next.FFTPV.DropTwoSource.source_drop_two_total,
    `RH080Next.FFTPV.DropTwoSource.roundData_outside]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source drop-two stage theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified drop-two stage axiom {root}: {axioms}"
    logInfo m!"FFT_DROP_TWO_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.DropTwoSource.source_drop_two_total]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.DropTwoSource.actual_six_statements,
      `RH080Next.FFTPV.DropTwoSource.initialize_drop,
      `RH080Next.FFTPV.DropTwoSource.move_execution,
      `RH080Next.FFTPV.DropTwoSource.loop_execution,
      `RH080Next.FFTPV.DropTwoSource.clear_execution,
      `RH080Next.FFTPV.DropTwoSource.rounding_execution,
      `RH080Next.FFTPV.DropTwoSource.roundData_magnitude,
      `RH080Next.FFTPV.DropTwoSource.lost_zero_iff_remainder,
      `RH080Next.FFTPV.DropTwoSource.increment_status_zero,
      `RH080Next.FFTPV.IncrementSource.increment_words_call_framed,
      `RH080Next.FFTPV.IncrementSource.returned_call_unique,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution] do
    unless dependencies.contains child do throwError "Missing actual source/drop-two/math link {child}"
  logInfo m!"FFT_DROP_TWO_AUDIT_PASS roots=13 closure={dependencies.toList.length} actual-character-syntax-both-profiles real-lost-declaration-and-counter-reset actual-overlapping-forward-moves unsigned-no-wrap preserved-unread-limbs actual-upper-zero-stores source-increment-no-overflow exact-ceiling-by10pow18 all-permitted-stage-executions no-native no-sorry MAIN_STAGE_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
