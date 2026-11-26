/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FFTZeroSliceCall
open Lean Elab Command
private partial def actualClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root :: rest, seen =>
    if seen.contains root then actualClosure env rest seen else
    let seen := root :: seen
    if !(root.toString.startsWith "RH080Next." || root.toString.startsWith "GoldbachDirect." ||
      root.toString.startsWith "_private.") then actualClosure env rest seen
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
    `RH080Next.FFTPV.ZeroSlice.zeroData_inside,
    `RH080Next.FFTPV.ZeroSlice.zeroData_outside,
    `RH080Next.FFTPV.ZeroSlice.contents_execution,
    `RH080Next.FFTPV.ZeroSlice.loop_execution,
    `RH080Next.FFTPV.ZeroSlice.loop_frame,
    `RH080Next.FFTPV.ZeroSlice.loop_postcondition,
    `RH080Next.FFTPV.ZeroSlice.initialize_parameters,
    `RH080Next.FFTPV.ZeroSlice.zero_words_call,
    `RH080Next.FFTPV.ZeroSlice.every_zero_words_call,
    `RH080Next.FFTPV.ZeroSlice.source_zero_slice_total]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing typed source theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unexpected axiom {root}: {axioms}"
    logInfo m!"ZERO_SLICE_AXIOMS {root}: {axioms}"
  let closure := actualClosure env [`RH080Next.FFTPV.ZeroSlice.source_zero_slice_total] []
  for required in #[
    `RH080Next.FFTRecursivePV.actual_source_syntax,
    `RH080Next.FFTRecursivePV.checkedSyntax_sound,
    `GoldbachDirect.Correspondence.supportedProgramSyntax_sound,
    `RH080Next.FFTPV.ZeroSlice.initialize_parameters,
    `RH080Next.FFTPV.ZeroSlice.contents_execution,
    `RH080Next.FFTPV.ZeroSlice.loop_execution,
    `RH080Next.FFTPV.ZeroSlice.loop_postcondition,
    `RH080Next.FFTPV.ZeroSlice.every_zero_words_call,
    `RH080Next.FFTPV.PureDeterminism.simple_unique,
    `GoldbachDirect.PureEval.eval_sound,
    `GoldbachDirect.PureEval.place_sound] do
    unless closure.contains required do throwError "Actual source/model dependency absent: {required}"
  logInfo m!"ZERO_SLICE_SOURCE_AUDIT_PASS roots={roots.size} closure={closure.length}"
