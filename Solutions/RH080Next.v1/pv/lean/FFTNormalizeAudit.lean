/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeProfiles
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
  let roots:=#[`RH080Next.FFTPV.NormalizeSource.division_execution,
    `RH080Next.FFTPV.NormalizeSource.source_division_execution,
    `RH080Next.FFTPV.NormalizeSource.actual_w4_total_divisions,
    `RH080Next.FFTPV.NormalizeSource.actual_fap_total_division,
    `RH080Next.FFTPV.NormalizeSource.actual_w4_quad_divisions,
    `RH080Next.FFTPV.NormalizeSource.actual_fap_quad_divisions]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source normalization division theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified normalization division axiom {root}: {axioms}"
    logInfo m!"FFT_NORMALIZE_DIVISION_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.NormalizeSource.source_division_execution]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.DivideSource.divide_small_total,
      `RH080Next.FFTPV.DivideSource.roundedData_value,
      `RH080Next.FFTPV.DivideSource.returned_call_unique,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution] do
    unless dependencies.contains child do throwError "Missing actual source/ceil-division/math link {child}"
  logInfo m!"FFT_NORMALIZE_DIVISION_AUDIT_PASS roots=6 closure={dependencies.toList.length} actual-character-syntax-both-profiles actual-total-and-quad-division-locators source-callee-and-every-assignment-execution uint64-guards exact-upward-integer-quotient preserved-workspace-outside-six-words no-native no-sorry INDIVIDUAL_SOURCE_CALL_CONTRACTS_ONLY_MAIN_SEQUENCE_AND_ANT_CONNECTION_PENDING"
