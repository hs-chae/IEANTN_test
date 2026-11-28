import FFTMainRecursiveStatement
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def statementProofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | _=>none
private partial def statementProofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then statementProofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match statementProofValue? info with
      | some body=>statementProofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>statementProofClosure env rest seen
    | none=>statementProofClosure env rest seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[
    `RH080Next.FFTPV.MainCertificate.front_buffer_arrays,
    `RH080Next.FFTPV.MainCertificate.call_from_front,
    `RH080Next.FFTPV.MainRecursiveStatement.actual_w4_statement,
    `RH080Next.FFTPV.MainRecursiveStatement.actual_fap_statement,
    `RH080Next.FFTPV.MainRecursiveStatement.source_arguments,
    `RH080Next.FFTPV.MainRecursiveStatement.source_arguments_pure,
    `RH080Next.FFTPV.MainRecursiveStatement.locals_after_recursive,
    `RH080Next.FFTPV.MainRecursiveStatement.execute,
    `RH080Next.FFTPV.MainRecursiveStatement.Ready.partialSum_receipt,
    `RH080Next.FFTRecursivePV.actual_source_syntax,
    `RH080Next.FapFFTRecursivePV.actual_source_syntax]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual main FFT Call theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted main FFT Call axiom {root}: {axioms}"
    logInfo m!"FFT_MAIN_RECURSIVE_STATEMENT_AXIOMS {root}: {axioms}"
  let dependencies:=statementProofClosure env [`RH080Next.FFTPV.MainRecursiveStatement.execute]
  for child in #[
      `RH080Next.FFTPV.MainCertificate.call_from_front,
      `RH080Next.FFTPV.MainCertificate.front_buffer_arrays,
      `RH080Next.FFTPV.MainCertificate.helpers,
      `RH080Next.FFTPV.MainCertificate.loaded_normalized,
      `RH080Next.FFTPV.MainCertificate.Certificate.output_norm,
      `RH080Next.FFTPV.RecursiveSource.source_certificate_recursive_total,
      `RH080Next.FFTPV.MainRecursiveStatement.source_arguments,
      `RH080Next.FFTPV.MainRecursiveStatement.locals_after_recursive,
      `RH080Next.FFTPV.StatusCall.assignment_execution,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution,
      `RH080Next.FFTPV.RecursiveSource.CallPost.output_sum_fields,
      `RH080Next.FFTPV.RecursiveSource.CallPost.workOutside,
      `RH080Next.FFTPV.MainSuffix.FrontReady.accumulatorsZero] do
    unless dependencies.contains child do throwError "Missing actual source/input/FFT/output/frame proof link {child}"
  logInfo m!"FFT_MAIN_RECURSIVE_STATEMENT_AUDIT_PASS roots={roots.size} closure={dependencies.toList.length} exact-body22 actual-nine-arguments actual-source-recursion kernel-certificate-consumed every-permitted-execution status-zero full-main-locals loader-j-slot preserved-four-arrays derived-output-fields total-and-quad-zero no-output-oracle no-new-norm-premise no-native no-sorry"
