/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FFTFixedMultiplySuffixSource
open Lean Elab Command

private partial def actualClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root :: rest, seen =>
    if seen.contains root then actualClosure env rest seen else
    let seen := root :: seen
    if !(root.toString.startsWith "RH080Next." || root.toString.startsWith "GoldbachDirect." || root.toString.startsWith "_private.") then
      actualClosure env rest seen
    else match env.find? root with
      | none => actualClosure env rest seen
      | some info =>
        let names := info.type.getUsedConstants
        let names := match info with
          | .thmInfo t => names ++ t.value.getUsedConstants
          | .defnInfo t => names ++ t.value.getUsedConstants
          | _ => names
        actualClosure env (names.toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let roots := #[
    `RH080Next.FFTPV.MultiplySuffix.actual_suffix,
    `RH080Next.FFTPV.MultiplySuffix.sign_execution,
    `RH080Next.FFTPV.MultiplySuffix.every_lost_loop,
    `RH080Next.FFTPV.MultiplySuffix.every_copy_loop,
    `RH080Next.FFTPV.MultiplySuffix.prepare_execution,
    `RH080Next.FFTPV.MultiplySuffix.suffix_execution,
    `RH080Next.FFTPV.MultiplySuffix.suffix_total,
    `RH080Next.FFTPV.MultiplySuffix.increment_overflow_unique_at,
    `RH080Next.FFTPV.MultiplySuffix.rounding_frame,
    `RH080Next.FFTPV.MultiplySuffix.prefix_frame,
    `RH080Next.FFTPV.MultiplySuffix.suffix_framed,
    `RH080Next.FFTPV.MultiplySuffix.source_suffix_total,
    `RH080Next.FFTPV.MultiplySuffix.suffix_output_equation,
    `RH080Next.FFTPV.MultiplySuffix.finalData_successful,
    `RH080Next.FFTPV.MultiplySuffix.finalStatus_eq_zero]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected axiom {root}: {axioms}"
    logInfo m!"MULTIPLY_SUFFIX_AXIOMS {root}: {axioms}"
  let closure := actualClosure env roots.toList []
  for required in #[
    `RH080Next.FFTRecursivePV.actual_source_syntax,
    `RH080Next.FFTRecursivePV.checkedSyntax_sound,
    `GoldbachDirect.Correspondence.supportedProgramSyntax_sound,
    `GoldbachDirect.checkedSource_lexes,
    `RH080Next.FFTPV.MultiplySuffix.actual_suffix,
    `RH080Next.FFTPV.MultiplySuffix.suffix_framed,
    `RH080Next.FFTPV.MultiplySuffix.suffix_total,
    `RH080Next.FFTPV.MultiplySuffix.rounding_unique_at,
    `RH080Next.FFTPV.MultiplySuffix.rounding_frame,
    `RH080Next.FFTPV.IncrementSource.increment_words_call_framed,
    `RH080Next.FFTPV.CanonicalSource.canonical_sign_call_framed,
    `RH080Next.FFTPV.CanonicalSource.call_unique,
    `RH080Next.FFT.Limbs.successful_product_suffix,
    `GoldbachDirect.PureEval.eval_sound,
    `GoldbachDirect.PureEval.place_sound] do
    unless closure.contains required do throwError "Required source/execution/math dependency absent: {required}"
  for name in closure do
    if name.toString.contains "ofReduceBool" || name.toString.contains "native_decide" || name == `sorryAx then
      throwError "Forbidden execution leaf {name}"
  logInfo m!"MULTIPLY_SUFFIX_HELPER_AUDIT_PASS roots={roots.size} closure={closure.length} full_C_caller_and_ANT_PV=false"
