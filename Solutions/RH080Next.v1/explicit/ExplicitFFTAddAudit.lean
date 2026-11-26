/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddSource
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
  let roots:=#[(`RH080Next.FFTPV.AddSource.source_fixed_add_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.AddSource.fap_source_fixed_add_total,`RH080Next.FapFFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.AddSource.recursive_source_fixed_add_total,`RH080Next.FFTRecursivePV.actual_source_syntax),
    (`RH080Next.FFTPV.AddSource.fap_recursive_source_fixed_add_total,`RH080Next.FapFFTRecursivePV.actual_source_syntax)]
  for (root,syntaxProof) in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual source helper {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden helper axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,
        `RH080Next.FFTPV.AddSource.actual_body,
        `RH080Next.FFTPV.AddSource.initialize_signs,
        `RH080Next.FFTPV.AddSource.flip_sign_execution,
        `RH080Next.FFTPV.AddSource.initialize_loop_vars,
        `RH080Next.FFTPV.AddSource.currentData_unread,
        `RH080Next.FFTPV.AddSource.Arrays.store_digit,
        `RH080Next.FFTPV.AddSource.add_loop_execution,
        `RH080Next.FFTPV.AddSource.swap_execution,
        `RH080Next.FFTPV.AddSource.sub_loop_execution,
        `RH080Next.FFTPV.AddSource.choose_sign_execution,
        `RH080Next.FFTPV.AddSource.store_sign_execution,
        `RH080Next.FFTPV.AddSource.arithmetic_execution,
        `RH080Next.FFTPV.AddSource.canonical_execution,
        `RH080Next.FFTPV.AddSource.fixed_add_call,
        `RH080Next.FFTPV.AddSource.returned_call_unique,
        `RH080Next.FFTPV.AddSource.finalData_integer_correct,
        `RH080Next.FFTPV.CompareSource.magnitude_compare_call,
        `RH080Next.FFTPV.CanonicalSource.canonical_sign_total,
        `RH080Next.FFTPV.CanonicalSource.call_unique,
        `RH080Next.FFTPV.ApplicationPureCall.expression_call_unique,
        `RH080Next.FFTPV.ApplicationPureCall.declare_call_unique,
        `GoldbachDirect.PureArgs.args_sound,
        `RH080Next.FFTPV.CompareSource.while_unique,
        `RH080Next.FFTPV.WordArrays.binary64_sub,
        `RH080Next.FFT.Limbs.fixedAddMath_correct,
        `RH080Next.FFT.Limbs.canonical_sign_preserves] do
      unless used.contains needed do throwError "Source/math helper proof missing {root}->{needed}"
    logInfo m!"FFT_ADD_SOURCE_AXIOMS {root}: {axioms}"
  logInfo "FFT_ADD_SOURCE_AUDIT_PASS four-actual-C-files independently-parsed full-Call all-executions all-argument-orders signed-integer-add-sub alias-safe no-wrap temporary-lifetimes caller-frame Std3 final-ANT-connection-pending"
