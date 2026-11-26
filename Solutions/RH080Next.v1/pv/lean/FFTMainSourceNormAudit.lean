/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSourceNormProgram
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
  let roots:=#[`RH080Next.FFTPV.MainSuffix.raw_to_loaded,`RH080Next.FFTPV.MainSuffix.sum_normalize_quad,`RH080Next.FFTPV.MainSuffix.actual_successful_suffix,`RH080Next.FFTPV.MainSuffix.norm_suffix_total,`RH080Next.FFTPV.MainSuffix.every_norm_suffix,`RH080Next.FFTPV.MainSuffix.normAnswer_fits,`RH080Next.FFTPV.MainSuffix.every_norm_call,`RH080Next.FFTPV.MainSuffix.norm_call_exists,`RH080Next.FFTPV.MainSuffix.successful_norm_call,`RH080Next.FFTPV.MainSuffix.source_norm_program_total]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing whole norm-source theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified whole norm-source axiom {root}: {axioms}"
    logInfo m!"FFT_MAIN_SOURCE_NORM_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.MainSuffix.source_norm_program_total]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,`RH080Next.FapFFTRecursivePV.actual_source_syntax,`RH080Next.FFTPV.MainAllocation.bind_norm_parameter,`RH080Next.FFTPV.MainAllocation.four_allocations,`RH080Next.FFTPV.MainAllocation.InitializedView.all_guard_steps,`RH080Next.FFTPV.MainAllocation.InitializedView.all_zero_steps,`RH080Next.FFTPV.MainRootBirth.from_initialized,`RH080Next.FFTPV.RootSource.initialize_root_total,`RH080Next.FFTPV.TwiddleSource.source_construct_table,`RH080Next.FFTPV.InputLoader.input_loader_total,`RH080Next.FFTPV.MainRecursiveStatement.execute,`RH080Next.FFTPV.RecursiveSource.source_certificate_recursive_total,`RH080Next.FFTPV.RecursiveSource.CallPost.output_sum_fields,`RH080Next.FFTPV.MainRecursiveStatement.Ready.partialSum_receipt,`RH080Next.FFTPV.OutputSumSource.source_loop_execution,`RH080Next.FFTPV.DropTwoSource.source_drop_two_total,`RH080Next.FFTPV.NormalizeSource.source_total_execution,`RH080Next.FFTPV.QuadSource.source_quad_stage_total,`RH080Next.FFTPV.NormalizeSource.source_quad_execution,`RH080Next.FFTPV.AnswerSource.source_answer_total,`RH080Next.FFTPV.MainAllocation.FreeView.source_final_total,`RH080Next.FFTPV.MainAllocation.norm_call_result_of_suffix,`RH080Next.FFTPV.MainAllocation.every_norm_call_prefix] do
    unless dependencies.contains child do throwError "Missing actual whole-source/initialization/execution/arithmetic/output link {child}"
  logInfo m!"FFT_MAIN_SOURCE_NORM_AUDIT_PASS roots=10 closure={dependencies.toList.length} actual-independent-source-syntax-both-profiles real-parameter-calloc-null-guards-typed-zero-root-table-loader every-recursive-execution actual-FFT-samples-to-certificate-sum real-counter-shift-ceil-quadrature-normalization-guard-free-return whole-Call-existence all-Call-MAX-or-source-answer no-successful-application-oracle no-native no-sorry FIXED_CERTIFICATE_SCALAR_AND_ACTUAL_ANT_INSTANTIATION_PENDING"
