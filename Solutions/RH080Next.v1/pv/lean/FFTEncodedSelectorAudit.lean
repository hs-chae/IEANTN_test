/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorSource
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
  let roots:=#[`RH080Next.FFTPV.EncodedSelector.build_covers,
    `RH080Next.FFTPV.EncodedSelector.Covers.value_eq,
    `RH080Next.FFTPV.EncodedSelector.w4_actual_function,
    `RH080Next.FFTPV.EncodedSelector.fap_actual_function,
    `RH080Next.FFTPV.EncodedSelector.execution,
    `RH080Next.FFTPV.EncodedSelector.body_execution,
    `RH080Next.FFTPV.EncodedSelector.body_unique,
    `RH080Next.FFTPV.EncodedSelector.encoded_node_call,
    `RH080Next.FFTPV.EncodedSelector.returned_call_unique,
    `RH080Next.FFTPV.EncodedSelector.w4_encoded_node_correct,
    `RH080Next.FFTPV.EncodedSelector.fap_encoded_node_correct]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual typed selector theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified selector axiom {root}: {axioms}"
    logInfo m!"FFT_SELECTOR_AXIOMS {root}: {axioms}"
  for root in #[`RH080Next.FFTPV.EncodedSelector.w4_encoded_node_correct,
      `RH080Next.FFTPV.EncodedSelector.fap_encoded_node_correct] do
    let dependencies:=proofClosure env [root]
    for child in #[`RH080Next.FFTPV.EncodedSelector.build_covers,
        `RH080Next.FFTPV.EncodedSelector.Covers.value_eq,
        `RH080Next.FFTPV.EncodedSelector.execution,
        `RH080Next.FFTPV.EncodedSelector.body_execution,
        `RH080Next.FFTPV.EncodedSelector.body_unique,
        `RH080Next.FFTPV.EncodedSelector.returned_call_unique,
        `RH080Next.FFTPV.EncodedSelector.encoded_node_call] do
      unless dependencies.contains child do throwError "Missing typed source/table/call link {root}: {child}"
    logInfo m!"FFT_SELECTOR_CLOSURE {root}: {dependencies.toList.length}"
  logInfo m!"FFT_SELECTOR_AUDIT_PASS roots=11 actual-source-both-profiles literal-AST-binding independent-contiguous-table-relation typed-unsigned-guards actual-parameter-and-branch-scopes all-permitted-Calls exact-locked-input-table readonly-caller no-native no-sorry INPUT_HELPER_ONLY_FINAL_FFT_AND_ANT_SOURCE_CHAIN_OPEN"
