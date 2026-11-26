/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideSource
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
  let roots:=#[(`RH080Next.FFTPV.DivideSource.source_divide_small_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.DivideSource.fap_source_divide_small_total,`RH080Next.FapFFTPV.actual_source_syntax)]
  for (root,syntaxProof) in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual source helper {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden helper axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,
        `RH080Next.FFTPV.DivideSource.actual_body,
        `RH080Next.FFTPV.DivideSource.initialize_parameters,
        `RH080Next.FFTPV.DivideSource.currentData_step,
        `RH080Next.FFTPV.DivideSource.digit_prefix_execution,
        `RH080Next.FFTPV.DivideSource.loop_execution,
        `RH080Next.FFTPV.DivideSource.rounding_execution,
        `RH080Next.FFTPV.DivideSource.divide_small_call,
        `RH080Next.FFTPV.DivideSource.returned_call_unique,
        `RH080Next.FFTPV.DivideSource.roundedData_value,
        `RH080Next.FFTPV.DivideSource.rounded_increment_carry_zero,
        `RH080Next.FFTPV.IncrementSource.increment_words_call_framed,
        `RH080Next.FFTPV.IncrementSource.returned_call_unique,
        `RH080Next.FFTPV.ApplicationPureCall.return_call_unique,
        `GoldbachDirect.PureArgs.args_sound,
        `RH080Next.FFTPV.CompareSource.while_unique,
        `RH080Next.FFTPV.PureDeterminism.eval_unique,
        `RH080Next.FFTPV.WordArrays.binary64_mul,
        `RH080Next.FFTPV.WordArrays.binary64_div,
        `RH080Next.FFTPV.WordArrays.binary64_mod,
        `RH080Next.FFT.Limbs.divideDigits_value,
        `RH080Next.FFT.Limbs.divideDigits_quotient_remainder,
        `RH080Next.FFT.Limbs.divideDigits_bounds,
        `RH080Next.FFT.Limbs.incrementDigits_value,
        `RH080Next.FFT.Limbs.incrementDigits_no_overflow] do
      unless used.contains needed do throwError "Source/math helper proof missing {root}->{needed}"
    logInfo m!"FFT_DIVIDE_SOURCE_AXIOMS {root}: {axioms}"
  logInfo "FFT_DIVIDE_SOURCE_AUDIT_PASS two-actual-C-files independently-parsed full-Call all-executions all-argument-orders exact-floor-or-ceiling no-wrap temporary-lifetimes caller-frame Std3 whole-FFT-norm-still-open"
