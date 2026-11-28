/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderSource
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
  let root:=`RH080Next.FFTPV.InputLoader.source_input_loader_total
  let some (.thmInfo _) := env.find? root | throwError "Missing actual source input-loader contract"
  let axioms ← collectAxioms root
  unless axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains) do throwError "Forbidden input-loader axiom: {axioms}"
  let used:=proofClosure env [root]
  for needed in #[`RH080Next.FFTPV.InputLoader.Profile.actual_syntax,
      `RH080Next.FFTPV.InputLoader.Profile.source_loop,
      `RH080Next.FFTPV.InputLoader.input_loader_total,
      `RH080Next.FFTPV.InputLoader.loop_execution,
      `RH080Next.FFTPV.InputLoader.row_execution,
      `RH080Next.FFTPV.InputLoader.source_row,
      `RH080Next.FFTPV.InputLoader.BodyView.prefix_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.e_birth,
      `RH080Next.FFTPV.InputLoader.BodyView.magnitude_branch_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.preparation_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.raw_stores_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.canonical_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.mirror_execution,
      `RH080Next.FFTPV.InputLoader.BodyView.advance_execution,
      `RH080Next.FFTPV.InputLoader.currentData_middle,
      `RH080Next.FFTPV.InputLoader.currentData_decoded,
      `RH080Next.FFTPV.InputLoader.completed_input_pair,
      `RH080Next.FFTPV.InputLoader.fap_coefficient,
      `RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.EncodedSelector.encoded_node_call,
      `RH080Next.FFTPV.EncodedSelector.fap_encoded_node_correct,
      `RH080Next.FFTPV.EncodedSelector.w4_encoded_node_correct,
      `RH080Next.FFTPV.InputCell.pair_value,
      `RH080Next.FFTPV.CopyLoop.copy_words_call_framed,
      `RH080Next.FFTPV.CanonicalSource.canonical_sign_call_framed,
      `RH080Next.FFTPV.RootSource.every_while_next,
      `GoldbachDirect.PureArgs.args_sound] do
    unless used.contains needed do throwError "Missing actual source/math loader dependency {needed}"
  logInfo m!"FFT_INPUT_LOADER_AXIOMS {axioms}"
  logInfo "FFT_INPUT_LOADER_AUDIT_PASS two-original-recursive-C-sources exact400and2520inputs all-grid-positions actual14-statement-row whole-loop every-execution source-selector-to-existing-integer-model no-wrap nested-lifetimes real-memory caller-frame Std3 main-ANT-connection-pending"
