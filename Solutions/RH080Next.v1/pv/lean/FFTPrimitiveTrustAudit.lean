/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDecodedSeed
import FapFFTDecodedSeed
import FFTZeroCall
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
  let roots:=#[`RH080Next.FFTPV.Certified.source_initializer_seed_bound,
    `RH080Next.FapFFTPV.Certified.source_initializer_seed_bound,
    `RH080Next.FFTPV.ZeroLoop.source_zero_words_execution,
    `RH080Next.FFTPV.ZeroLoop.caller_byte_birth]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing primitive theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unverified primitive axiom {root}: {axioms}"
    logInfo m!"FFT_PRIMITIVE_AXIOMS {root}: {axioms}"
  for (ns,root,seedMath) in #[
      (`RH080Next.FFTPV,`RH080Next.FFTPV.Certified.source_initializer_seed_bound,
        `RH080Next.FFT.rootSeed_error),
      (`RH080Next.FapFFTPV,`RH080Next.FapFFTPV.Certified.source_initializer_seed_bound,
        `RH080Next.FFT.rootSeed17_error)] do
    let dependencies:=proofClosure env [root]
    for child in #[ns++`actual_source_syntax,ns++`Certified.actual_root_result,
        ns++`Certified.invokeRoot_sound,ns++`Certified.actual_root_execution,
        ns++`Certified.decoded_actual_seed,seedMath] do
      unless dependencies.contains child do throwError "Source initializer proof missing {root}->{child}"
  let zero:=proofClosure env [`RH080Next.FFTPV.ZeroLoop.source_zero_words_execution]
  for child in #[`RH080Next.FFTPV.actual_source_syntax,
      `RH080Next.FFTPV.ZeroLoop.zero_words_call,`RH080Next.FFTPV.ZeroLoop.loop_execution,
      `RH080Next.FFTPV.ZeroLoop.loop_body_execution,
      `RH080Next.FFTPV.WordArrays.zeroPrefix_store,
      `RH080Next.FFTPV.ZeroLoop.final_word_representation] do
    unless zero.contains child do throwError "Actual zero helper proof missing {child}"
  logInfo "FFT_PRIMITIVE_AUDIT_PASS roots=4 source-syntax-execution-true-seed-and-zero-loop-consumed no-native no-sorry canonical-caller-frames-only full-FFT-OPEN"
