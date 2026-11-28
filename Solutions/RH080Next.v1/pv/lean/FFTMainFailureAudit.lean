import FFTMainFailureCall
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | _=>none
private partial def proofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then proofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match proofValue? info with
      | some body=>proofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>proofClosure env rest seen
    | none=>proofClosure env rest seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[
    `RH080Next.FFTPV.MainAllocation.calloc_expression_cases,
    `RH080Next.FFTPV.MainAllocation.calloc_declaration_cases,
    `RH080Next.FFTPV.MainAllocation.NullableView.initial,
    `RH080Next.FFTPV.MainAllocation.NullableView.count_eval,
    `RH080Next.FFTPV.MainAllocation.NullableView.birth_cases,
    `RH080Next.FFTPV.MainAllocation.NullableView.nonnull_view,
    `RH080Next.FFTPV.MainAllocation.NullableView.allocation_cons,
    `RH080Next.FFTPV.MainAllocation.every_four_allocations,
    `RH080Next.FFTPV.MainAllocation.failure_return_flow,
    `RH080Next.FFTPV.MainAllocation.free_statement_normal,
    `RH080Next.FFTPV.MainAllocation.cleanup_return_flow,
    `RH080Next.FFTPV.MainAllocation.failure_block_flow,
    `RH080Next.FFTPV.MainAllocation.NullableView.null_test,
    `RH080Next.FFTPV.MainAllocation.NullableView.guard_cases,
    `RH080Next.FFTPV.MainAllocation.NullableView.guards_cases,
    `RH080Next.FFTPV.MainAllocation.every_guard_prefix,
    `RH080Next.FFTPV.MainAllocation.execution_append_cases,
    `RH080Next.FFTPV.MainAllocation.every_norm_prefix,
    `RH080Next.FFTPV.MainAllocation.every_w4_norm_prefix,
    `RH080Next.FFTPV.MainAllocation.every_fap_norm_prefix,
    `RH080Next.FFTPV.MainAllocation.failure_source_body,
    `RH080Next.FFTPV.MainAllocation.failure_source_parameters,
    `RH080Next.FFTPV.MainAllocation.failure_source_result,
    `RH080Next.FFTPV.MainAllocation.failure_source_no_labels,
    `RH080Next.FFTPV.MainAllocation.no_labels_body_execution,
    `RH080Next.FFTPV.MainAllocation.every_norm_call_prefix,
    `RH080Next.FFTRecursivePV.actual_source_syntax,
    `RH080Next.FapFFTRecursivePV.actual_source_syntax]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing source failure-classification theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard failure-classification axiom {root}: {axioms}"
    logInfo m!"FFT_MAIN_FAILURE_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.MainAllocation.every_norm_call_prefix]
  for child in #[
      `RH080Next.FFTPV.MainAllocation.bind_norm_parameter,
      `RH080Next.FFTPV.MainAllocation.calloc_call_cases,
      `RH080Next.FFTPV.MainAllocation.calloc_expression_cases,
      `RH080Next.FFTPV.MainAllocation.calloc_declaration_cases,
      `RH080Next.FFTPV.MainAllocation.NullableView.birth_cases,
      `RH080Next.FFTPV.MainAllocation.every_four_allocations,
      `RH080Next.FFTPV.MainAllocation.cleanup_return_flow,
      `RH080Next.FFTPV.MainAllocation.NullableView.guards_cases,
      `RH080Next.FFTPV.MainAllocation.every_norm_prefix,
      `RH080Next.FFTPV.MainAllocation.failure_source_no_labels,
      `RH080Next.FFTPV.MainAllocation.no_labels_body_execution] do
    unless dependencies.contains child do throwError "Missing actual allocation/failure/parameter source link {child}"
  logInfo m!"FFT_MAIN_FAILURE_AUDIT_PASS roots={roots.size} closure={dependencies.toList.length} every-source-calloc-choice real-parameter-bind NULL-or-fresh actual-pointer-slots raw-zero-byte-arrays every-actual-NULL-guard exact-MAX-return every-actual-norm-Call actual-nonNULL-state actual-body-drop8 real-return-conversion real-caller-scope-finish termination-explicit no-always-success no-native no-sorry GENERIC_MEMORY_CONTRACT_REQUIRED_SUCCESS_SUFFIX_AND_ANT_INTEGRATION_SEPARATE"
