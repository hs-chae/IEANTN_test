import FFTMainIOOutput
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def ioProofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | .opaqueInfo info=>some info.value
  | _=>none
private partial def ioClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then ioClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match ioProofValue? info with
      | some value=>ioClosure env (value.getUsedConstants.toList++rest) seen
      | none=>ioClosure env rest seen
    | none=>ioClosure env rest seen
run_cmd do
  let env←getEnv
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let roots:=#[
    `RH080Next.FFTPV.MainIO.bindParameters_foreign,
    `RH080Next.FFTPV.MainIO.call_foreign_frame,
    `RH080Next.FFTPV.MainIO.call_extend_foreign,
    `RH080Next.FFTPV.MainIO.decimalLF_length,
    `RH080Next.FFTPV.MainIO.memoryOnly_hasMemory,
    `RH080Next.FFTPV.MainIO.memoryOnly_sound,
    `RH080Next.FFTPV.MainIO.io_hasMemory,
    `RH080Next.FFTPV.MainIO.io_sound,
    `RH080Next.FFTPV.MainIO.memoryOnly_foreign_frame,
    `RH080Next.FFTPV.MainIO.memoryOnly_call_in_io,
    `RH080Next.FFTPV.MainIO.printf_cases,
    `RH080Next.FFTPV.MainIO.literal_exact,
    `RH080Next.FFTPV.MainIO.two_arguments,
    `RH080Next.FFTPV.MainIO.norm_arguments,
    `RH080Next.FFTPV.MainIO.printf_arguments,
    `RH080Next.FFTPV.MainIO.every_printf_arguments,
    `RH080Next.FFTPV.MainIO.caller_well,
    `RH080Next.FFTPV.MainIO.mainEntry_well,
    `RH080Next.FFTPV.MainIO.main_body,
    `RH080Next.FFTPV.MainIO.source_main_call,
    `RH080Next.FFTPV.MainIO.actual_main_success,
    `RH080Next.FFTPV.MainIO.actual_main_partial_failure,
    `RH080Next.FFTPV.MainIO.main_parameters,
    `RH080Next.FFTPV.MainIO.main_result,
    `RH080Next.FFTPV.MainIO.actual_printf_call,
    `RH080Next.FFTPV.MainIO.printf_statement,
    `RH080Next.FFTPV.MainIO.list_association,
    `RH080Next.FFTPV.MainIO.body_association,
    `RH080Next.FFTPV.MainIO.every_main_call,
    `RH080Next.FFTPV.MainIO.result_value_eq,
    `RH080Next.FFTPV.MainIO.actual_result]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual main IO theorem {root}"
    let axioms←collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted main IO axiom {root}: {axioms}"
    logInfo m!"FFT_MAIN_IO_AXIOMS {root}: {axioms}"
  let successful:=ioClosure env [`RH080Next.FFTPV.MainIO.actual_result]
  for child in #[
      `RH080Next.FFTPV.MainIO.actual_main_success,
      `RH080Next.FFTPV.MainIO.source_main_call,
      `RH080Next.FFTPV.MainIO.printf_arguments,
      `RH080Next.FFTPV.MainIO.call_foreign_frame,
      `RH080Next.FFTPV.MainIO.call_extend_foreign,
      `RH080Next.FFTPV.MainSuffix.norm_call_exists,
      `RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax] do
    unless successful.contains child do throwError "Missing source/main/stdio success link {child}"
  let universal:=ioClosure env [`RH080Next.FFTPV.MainIO.result_value_eq]
  for child in #[
      `RH080Next.FFTPV.MainIO.every_main_call,
      `RH080Next.FFTPV.MainIO.every_printf_arguments,
      `RH080Next.FFTPV.MainIO.two_arguments,
      `RH080Next.FFTPV.MainIO.actual_printf_call,
      `RH080Next.FFTPV.MainSuffix.every_norm_call,
      `RH080Next.FFTPV.MainAllocation.every_norm_call_prefix,
      `RH080Next.FFTPV.MainSuffix.every_norm_suffix] do
    unless universal.contains child do throwError "Missing every-Call/source/NULL/stdio proof link {child}"
  logInfo m!"FFT_MAIN_IO_AUDIT_PASS roots={roots.size} successClosure={successful.toList.length} universalClosure={universal.toList.length} actual-full-main-call all-argument-orders exact-unsigned-decimal-LF partial-write-failures"
