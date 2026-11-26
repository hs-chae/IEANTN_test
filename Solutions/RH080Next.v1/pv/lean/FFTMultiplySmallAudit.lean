/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallSource
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
  let roots:=#[`RH080Next.FFTPV.MultiplySmallSource.row_carry_le,
    `RH080Next.FFTPV.MultiplySmallSource.initialize_parameters,
    `RH080Next.FFTPV.MultiplySmallSource.digit_prefix_execution,
    `RH080Next.FFTPV.MultiplySmallSource.loop_body_execution,
    `RH080Next.FFTPV.MultiplySmallSource.loop_execution,
    `RH080Next.FFTPV.MultiplySmallSource.multiply_small_call,
    `RH080Next.FFTPV.MultiplySmallSource.returned_call_unique,
    `RH080Next.FFTPV.MultiplySmallSource.multiply_small_value_total,
    `RH080Next.FFTPV.MultiplySmallSource.source_multiply_small_total,
    `RH080Next.FFTPV.MultiplySmallSource.fap_source_multiply_small_total]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing smallmultiply source theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified source axiom {root}: {axioms}"
    logInfo m!"FFT_SMALL_MULTIPLY_AXIOMS {root}: {axioms}"
  for (root,syntaxProof) in #[
      (`RH080Next.FFTPV.MultiplySmallSource.source_multiply_small_total,`RH080Next.FFTRecursivePV.actual_source_syntax),
      (`RH080Next.FFTPV.MultiplySmallSource.fap_source_multiply_small_total,`RH080Next.FapFFTRecursivePV.actual_source_syntax)] do
    let dependencies:=proofClosure env [root]
    for child in #[syntaxProof,`RH080Next.FFTPV.MultiplySmallSource.initialize_parameters,
        `RH080Next.FFTPV.MultiplySmallSource.t_eval,
        `RH080Next.FFTPV.MultiplySmallSource.digit_prefix_execution,
        `RH080Next.FFTPV.MultiplySmallSource.loop_body_execution,
        `RH080Next.FFTPV.MultiplySmallSource.loop_execution,
        `RH080Next.FFTPV.MultiplySmallSource.multiply_small_call,
        `RH080Next.FFTPV.MultiplySmallSource.returned_call_unique,
        `RH080Next.FFTPV.MultiplySmallSource.final_value,
        `RH080Next.FFTPV.MultiplySmallSource.row_carry_le,
        `RH080Next.FFTPV.WordArrays.binary64_mul,
        `RH080Next.FFTPV.WordArrays.word_store,
        `RH080Next.FFT.Limbs.row_value,
        `RH080Next.FFTPV.ApplicationBirthFrame.close_frame] do
      unless dependencies.contains child do throwError "Missing actual source/word/math link {root}->{child}"
    logInfo m!"FFT_SMALL_MULTIPLY_SOURCE_CLOSURE {root}: {dependencies.toList.length}"
  logInfo "FFT_SMALL_MULTIPLY_AUDIT_PASS roots=10 actual-source-both-profiles all-permitted-Calls factor0-supported no-wrap word-array-scope exact-integer-product-carry no-native no-sorry WHOLE_FFT_OPEN"
