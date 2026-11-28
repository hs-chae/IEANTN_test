/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveOutputSummary
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
  let roots:=#[`RH080Next.FFTPV.RecursiveSource.recursive_strong_total,
    `RH080Next.FFTPV.RecursiveSource.fap_recursive17_total,
    `RH080Next.FFTPV.RecursiveSource.w4_recursive24_total,
    `RH080Next.FFTPV.RecursiveSource.source_certificate_recursive_total,
    `RH080Next.FFTPV.RecursiveSource.CallPost.output_sum_fields,
    `RH080Next.FFTPV.RecursiveSource.CallPost.output_partialSum_receipt]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source recursion theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified recursive axiom {root}: {axioms}"
    logInfo m!"FFT_RECURSIVE_TOTAL_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.RecursiveSource.source_certificate_recursive_total]
  for child in #[`RH080Next.FFTPV.RecursiveSource.recursive_strong_total,
      `RH080Next.FFTPV.RecursiveSource.nonleaf_strong_contract,
      `RH080Next.FFTPV.RecursiveSource.leaf_strong_contract,
      `RH080Next.FFTPV.RecursiveSource.Header.View.total_header,
      `RH080Next.FFTPV.RecursiveSource.butterfly_contents,
      `RH080Next.FFTPV.RecursiveSource.butterfly_block,
      `RH080Next.FFTPV.RecursiveSource.butterfly_loop,
      `RH080Next.FFTPV.RecursiveSource.NormalSegment.while_next,
      `RH080Next.FFTPV.RecursiveSource.NormalSegment.while_false,
      `RH080Next.FFTPV.RecursiveSource.MergeProgress.merge_trace,
      `RH080Next.FFTPV.RecursiveSource.recursive_call_from_segment,
      `RH080Next.FFTPV.ComplexSource.complex_multiply_correct,
      `RH080Next.FFTPV.CopyLoop.copy_words_call_framed,
      `RH080Next.FFT.IntegerModel.ExecutionTrace.subtransform_norm_le,
      `RH080Next.FFTPV.RecursiveSource.CallPost.represent,
      `RH080Next.FFTPV.RecursiveSource.CallPost.output_eq_certificate,
      `RH080Next.FFTPV.RecursiveSource.input_mass_of_certificate,
      `RH080Next.FFTPV.RecursiveSource.source_table_stage_entries,
      `RH080Next.FFTPV.TwiddleSource.source_table_matches_trace] do
    unless dependencies.contains child do throwError "Missing consumed source/math helper {child}"
  logInfo m!"FFT_RECURSIVE_TOTAL_AUDIT_PASS roots=6 closure={dependencies.toList.length} source-total-every-call exact-integer-trace physical-output-slice protected-work-words actual-table-certificate-alignment no-native-numerical-leaves main-ANT-pending"
