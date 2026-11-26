/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSourceFinal
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
  let roots:=#[`RH080Next.FFTPV.StatusCall.slot_store_same,
    `RH080Next.FFTPV.StatusCall.assignment_execution,
    `RH080Next.FFTPV.StatusCall.status_eval_unique,
    `RH080Next.FFTPV.StatusCall.assignment_every_execution,
    `RH080Next.FFTPV.ComplexSource.initialize_call,
    `RH080Next.FFTPV.ComplexSource.pointer_offset_eval,
    `RH080Next.FFTPV.ComplexSource.initialize_view,
    `RH080Next.FFTPV.ComplexSource.component_properties,
    `RH080Next.FFTPV.ComplexSource.multiply_step,
    `RH080Next.FFTPV.ComplexSource.product_statements_execution,
    `RH080Next.FFTPV.ComplexSource.quotient_natAbs_le,
    `RH080Next.FFTPV.ComplexSource.rounded_product_magnitude_bound,
    `RH080Next.FFTPV.ComplexSource.sum_input_status_zero,
    `RH080Next.FFTPV.ComplexSource.add_step,
    `RH080Next.FFTPV.ComplexSource.sum_statements_execution,
    `RH080Next.FFTPV.ComplexSource.function_body_execution,
    `RH080Next.FFTPV.ComplexSource.returned_call_unique_at,
    `RH080Next.FFTPV.ComplexSource.complex_multiply_correct,
    `RH080Next.FFTPV.ComplexSource.resultPair_eq_integer_mul,
    `RH080Next.FFTPV.ComplexSource.source_complex_multiply_correct]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source complex helper theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified complex helper axiom {root}: {axioms}"
    logInfo m!"FFT_COMPLEX_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.ComplexSource.source_complex_multiply_correct]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.ComplexSource.initialize_call,
      `RH080Next.FFTPV.MultiplyParameters.initialize_parameters,
      `RH080Next.FFTPV.StatusCall.assignment_execution,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution,
      `RH080Next.FFTPV.MultiplyCall.fixed_multiply_correct_words,
      `RH080Next.FFTPV.AddSource.fixed_add_total,
      `RH080Next.FFTPV.AddSource.rawStatus_zero_of_sum_lt,
      `RH080Next.FFTPV.ComplexSource.sum_input_status_zero,
      `RH080Next.FFTPV.ComplexSource.product_statements_execution,
      `RH080Next.FFTPV.ComplexSource.sum_statements_execution,
      `RH080Next.FFTPV.ComplexSource.function_body_execution,
      `RH080Next.FFTPV.ComplexSource.returned_call_unique_at,
      `RH080Next.FFTPV.ComplexSource.complex_multiply_correct,
      `RH080Next.FFTPV.ComplexSource.resultPair_eq_integer_mul,
      `RH080Next.FFT.IntegerModel.mul,
      `GoldbachDirect.PureArgs.args_sound] do
    unless dependencies.contains child do throwError "Missing actual source/complex/integer link {child}"
  logInfo m!"FFT_COMPLEX_AUDIT_PASS roots=20 closure={dependencies.toList.length} actual-character-syntax-both-profiles actual-parameter-and-status-birth all-four-signed-floor-products two-signed-additions no-overflow normalized-pair same-object-word-frames all-permitted-Calls both-operand-orders all-argument-orders exact-FFT-integer-mul no-native no-sorry HELPER_CONTRACT_ONLY_WHOLE_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
