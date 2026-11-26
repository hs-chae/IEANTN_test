/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySourceFinal
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
  let roots:=#[`RH080Next.FFTPV.MultiplyParameters.initialize_parameters,
    `RH080Next.FFTPV.MultiplyParameters.begin_execution,
    `RH080Next.FFTPV.ProductOuter.every_source_product_core,
    `RH080Next.FFTPV.MultiplySuffix.suffix_execution,
    `RH080Next.FFTPV.MultiplySuffix.suffix_total,
    `RH080Next.FFTPV.MultiplySuffix.suffix_framed,
    `RH080Next.FFTPV.MultiplyCall.fixed_multiply_call,
    `RH080Next.FFTPV.MultiplyCall.returned_call_unique_at,
    `RH080Next.FFTPV.MultiplyCall.fixed_multiply_total,
    `RH080Next.FFTPV.MultiplyCall.fixed_multiply_call_framed,
    `RH080Next.FFTPV.MultiplyCall.fixed_multiply_normalized_call,
    `RH080Next.FFTPV.MultiplyCall.fixed_multiply_correct,
    `RH080Next.FFTPV.MultiplyCall.source_fixed_multiply_correct]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source multiplication helper theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified full multiply helper axiom {root}: {axioms}"
    logInfo m!"FFT_FIXED_MULTIPLY_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.MultiplyCall.source_fixed_multiply_correct]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.MultiplyParameters.initialize_parameters,
      `RH080Next.FFTPV.MultiplyParameters.initialized_core_execution,
      `RH080Next.FFTPV.ZeroSlice.zero_words_call,
      `RH080Next.FFTPV.ProductInner.source_five_digit_row,
      `RH080Next.FFTPV.ProductOuter.loop_execution,
      `RH080Next.FFTPV.ProductOuter.outer_loop_unique,
      `RH080Next.FFTPV.MultiplyParameters.begin_execution_framed,
      `RH080Next.FFTPV.MultiplySuffix.suffix_execution,
      `RH080Next.FFTPV.MultiplySuffix.suffix_total,
      `RH080Next.FFTPV.MultiplySuffix.suffix_framed,
      `RH080Next.FFTPV.MultiplySuffix.finalData_successful,
      `RH080Next.FFTPV.MultiplySuffix.finalStatus_eq_zero,
      `RH080Next.FFTPV.MultiplyCall.fixed_multiply_call_framed,
      `RH080Next.FFTPV.MultiplyCall.fixed_multiply_total,
      `RH080Next.FFTPV.MultiplyCall.fixed_multiply_correct,
      `RH080Next.FFT.Limbs.five_by_five_product,
      `RH080Next.FFTPV.WordArrays.word_store,
      `RH080Next.FFTPV.IncrementSource.increment_words_call_framed] do
    unless dependencies.contains child do throwError "Missing actual full-source/helper/math link {child}"
  logInfo m!"FFT_FIXED_MULTIPLY_AUDIT_PASS roots=13 closure={dependencies.toList.length} actual-character-syntax-both-profiles actual-parameter-and-initialization word-array-lifetimes no-wrap all-permitted-Calls exact-signed-floor normalized-output caller-frame no-native no-sorry HELPER_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
