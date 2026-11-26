/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FFTCopySourceFinal
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
    `RH080Next.FFTPV.WordArrays.slice_pointer_add,
    `RH080Next.FFTPV.WordArrays.word_store_with_rep,
    `RH080Next.FFTPV.CopyLoop.store_execution,
    `RH080Next.FFTPV.CopyLoop.contents_execution,
    `RH080Next.FFTPV.CopyLoop.block_execution,
    `RH080Next.FFTPV.CopyLoop.loop_execution,
    `RH080Next.FFTPV.CopyLoop.loop_frame,
    `RH080Next.FFTPV.CopyLoop.initialize_parameters,
    `RH080Next.FFTPV.CopyLoop.copy_words_call,
    `RH080Next.FFTPV.CopyLoop.loop_every_output,
    `RH080Next.FFTPV.CopyLoop.every_copy_words_call,
    `RH080Next.FFTPV.CopyLoop.source_copy_words_total]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected axiom {root}: {axioms}"
    logInfo m!"COPY_HELPER_AXIOMS {root}: {axioms}"
  let closure := actualClosure env [`RH080Next.FFTPV.CopyLoop.source_copy_words_total] []
  for required in #[
    `RH080Next.FFTRecursivePV.actual_source_syntax,
    `RH080Next.FFTRecursivePV.checkedSyntax_sound,
    `GoldbachDirect.Correspondence.supportedProgramSyntax_sound,
    `GoldbachDirect.checkedSource_lexes,
    `RH080Next.FFTPV.CopyLoop.initialize_parameters,
    `RH080Next.FFTPV.CopyLoop.store_execution,
    `RH080Next.FFTPV.CopyLoop.loop_execution,
    `RH080Next.FFTPV.CopyLoop.every_copy_words_call,
    `RH080Next.FFTPV.CopyLoop.loop_postcondition,
    `RH080Next.FFTPV.PureDeterminism.simple_unique,
    `GoldbachDirect.PureEval.eval_sound,
    `GoldbachDirect.PureEval.place_sound] do
    unless closure.contains required do throwError "Required source/execution dependency absent: {required}"
  for name in closure do
    if name.toString.contains "ofReduceBool" || name.toString.contains "native_decide" ||
        name == `sorryAx then throwError "Forbidden numerical execution leaf {name}"
  logInfo m!"COPY_HELPER_SOURCE_EXECUTION_AUDIT_PASS roots={roots.size} closure={closure.length}"
