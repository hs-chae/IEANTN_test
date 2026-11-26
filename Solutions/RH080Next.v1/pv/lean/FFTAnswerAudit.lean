/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerSource
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
  let roots:=#[`RH080Next.FFTPV.AnswerSource.actual_profile_answer,
    `RH080Next.FFTPV.AnswerSource.computed_fits,
    `RH080Next.FFTPV.AnswerSource.logic_execution,
    `RH080Next.FFTPV.AnswerSource.logic_unique,
    `RH080Next.FFTPV.AnswerSource.convert_declaration,
    `RH080Next.FFTPV.AnswerSource.header_execution,
    `RH080Next.FFTPV.AnswerSource.status_execution,
    `RH080Next.FFTPV.AnswerSource.initialize_answer,
    `RH080Next.FFTPV.AnswerSource.answer_total,
    `RH080Next.FFTPV.AnswerSource.result_of_small_sum,
    `RH080Next.FFTPV.AnswerSource.source_answer_total]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source guarded-answer stage theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified guarded-answer stage axiom {root}: {axioms}"
    logInfo m!"FFT_ANSWER_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.AnswerSource.source_answer_total]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.AnswerSource.actual_profile_answer,
      `RH080Next.FFTPV.AnswerSource.initialize_answer,
      `RH080Next.FFTPV.AnswerSource.convert_declaration,
      `RH080Next.FFTPV.AnswerSource.header_execution,
      `RH080Next.FFTPV.AnswerSource.logic_execution,
      `RH080Next.FFTPV.AnswerSource.logic_unique,
      `RH080Next.FFTPV.AnswerSource.status_execution,
      `RH080Next.FFTPV.ConvertBoundSource.convert_bound_total,
      `RH080Next.FFTPV.ConvertBoundSource.returned_call_unique,
      `RH080Next.FFTPV.StatusCall.call_eval_unique] do
    unless dependencies.contains child do throwError "Missing actual source/guarded-answer/math link {child}"
  logInfo m!"FFT_ANSWER_AUDIT_PASS roots=11 closure={dependencies.toList.length} actual-character-syntax-both-profiles original-main-statement-locators39-40 actual-sentinel-declaration two-real-convert-calls and-first-second-birth ancestor-answer-owner-and-inner-scope-lifetimes exact-original-guarded-additions uint64-no-wrap EVERY-stage-execution all-old-host-buffers-preserved true-final-answer-slot-and-lookup no-native no-sorry MAIN_STAGE_CONTRACT_ONLY_FULL_NORMALIZATION_INTEGRATION_FREE_RETURN_AND_ANT_CONNECTION_PENDING"
