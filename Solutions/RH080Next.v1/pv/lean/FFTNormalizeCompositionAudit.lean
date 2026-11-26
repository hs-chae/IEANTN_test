/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeSource
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
  let roots:=#[`RH080Next.FFTPV.NormalizeSource.total_execution,
    `RH080Next.FFTPV.NormalizeSource.quad_execution,
    `RH080Next.FFTPV.NormalizeSource.source_total_execution,
    `RH080Next.FFTPV.NormalizeSource.source_quad_execution,
    `RH080Next.FFTPV.NormalizeSource.actual_total_sequence,
    `RH080Next.FFTPV.NormalizeSource.actual_quad_sequence]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing complete source normalization division theorem theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified normalization division axiom {root}: {axioms}"
    logInfo m!"FFT_NORMALIZE_COMPOSITION_AXIOMS {root}: {axioms}"
  let dependencies:=proofClosure env [`RH080Next.FFTPV.NormalizeSource.source_total_execution,
    `RH080Next.FFTPV.NormalizeSource.source_quad_execution]
  for child in #[`RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.NormalizeSource.actual_total_sequence,
      `RH080Next.FFTPV.NormalizeSource.actual_quad_sequence,
      `RH080Next.FFTPV.NormalizeSource.total_execution,
      `RH080Next.FFTPV.NormalizeSource.quad_execution,
      `RH080Next.FFTPV.NormalizeSource.division_execution,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution] do
    unless dependencies.contains child do throwError "Missing actual finite source division composition {child}"
  logInfo m!"FFT_NORMALIZE_COMPOSITION_AUDIT_PASS roots=6 closure={dependencies.toList.length} actual-source-character-syntax both-original-profiles actual-total-one-or-two-calls actual-quad-three-calls exact-nested-upward-quotients zero-status normalized-source-produced-array physical-other-accumulator-preserved EVERY-source-sequence-execution no-native no-sorry MAIN_STAGE_CONTRACT_ONLY_FULL_MAIN_AND_ANT_CONNECTION_PENDING"
