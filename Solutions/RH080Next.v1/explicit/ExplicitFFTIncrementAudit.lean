/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTIncrementSource
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command
private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo i => some i.value
  | .defnInfo i => some i.value
  | _ => none
private partial def proofClosure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
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
  let roots:=#[(`RH080Next.FFTPV.IncrementSource.source_increment_words_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.IncrementSource.fap_source_increment_words_total,`RH080Next.FapFFTPV.actual_source_syntax)]
  for (root,syntaxProof) in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual source helper {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden helper axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,
        `RH080Next.FFTPV.IncrementSource.actual_body,
        `RH080Next.FFTPV.IncrementSource.initialize_parameters,
        `RH080Next.FFTPV.IncrementSource.currentData_step,
        `RH080Next.FFTPV.IncrementSource.digit_prefix_execution,
        `RH080Next.FFTPV.IncrementSource.loop_body_execution,
        `RH080Next.FFTPV.IncrementSource.loop_execution,
        `RH080Next.FFTPV.IncrementSource.increment_words_call,
        `RH080Next.FFTPV.IncrementSource.returned_call_unique,
        `RH080Next.FFTPV.CompareSource.while_unique,
        `RH080Next.FFTPV.PureDeterminism.eval_unique,
        `RH080Next.FFTPV.ApplicationBirthFrame.close_frame,
        `RH080Next.FFTPV.WordArrays.binary64_add,
        `RH080Next.FFTPV.WordArrays.binary64_div,
        `RH080Next.FFTPV.WordArrays.binary64_mod,
        `RH080Next.FFT.Limbs.incrementDigits_value,
        `RH080Next.FFT.Limbs.incrementDigits_bounds] do
      unless used.contains needed do throwError "Source/math helper proof missing {root}->{needed}"
    logInfo m!"FFT_INCREMENT_SOURCE_AXIOMS {root}: {axioms}"
  logInfo "FFT_INCREMENT_SOURCE_AUDIT_PASS two-actual-C-files independently-parsed full-Call all-executions safe-word-arithmetic exact-integer-increment temporary-lifetimes caller-frame Std3 whole-FFT-norm-still-open"
