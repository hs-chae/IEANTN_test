/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadSource
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
  let root:=`RH080Next.FFTPV.QuadSource.source_quad_stage_total
  let some (.thmInfo _) := env.find? root | throwError "Missing actual source quad contract"
  let axioms ← collectAxioms root
  unless axioms.all (#[`propext,`Classical.choice,`Quot.sound].contains) do throwError "Forbidden quad axiom: {axioms}"
  let used:=proofClosure env [root]
  for needed in #[`RH080Next.FFTPV.InputLoader.Profile.actual_syntax,
      `RH080Next.FFTPV.QuadSource.actual_stage,
      `RH080Next.FFTPV.QuadSource.quad_stage_total,
      `RH080Next.FFTPV.QuadSource.loop_execution,
      `RH080Next.FFTPV.QuadSource.row_execution,
      `RH080Next.FFTPV.QuadSource.View.prefix_execution,
      `RH080Next.FFTPV.QuadSource.View.e_birth,
      `RH080Next.FFTPV.QuadSource.View.absolute_execution,
      `RH080Next.FFTPV.QuadSource.View.magnitude_execution,
      `RH080Next.FFTPV.QuadSource.View.multiply_execution,
      `RH080Next.FFTPV.QuadSource.View.add_execution,
      `RH080Next.FFTPV.QuadSource.View.advance_execution,
      `RH080Next.FFTPV.QuadSource.View.factor_evaluation,
      `RH080Next.FFTPV.QuadSource.multiply_small_zero,
      `RH080Next.FFTPV.QuadSource.fap_scale_execution,
      `RH080Next.FFTPV.QuadSource.raw_quad_model,
      `RH080Next.FFTPV.QuadSource.abs_coefficient,
      `RH080Next.FFTPV.QuadSource.factor_bound,
      `RH080Next.FFTPV.QuadSource.partialQuad_bound,
      `RH080Next.FFTPV.InputLoader.fap_coefficient,
      `RH080Next.FFTRecursivePV.actual_source_syntax,
      `RH080Next.FapFFTRecursivePV.actual_source_syntax,
      `RH080Next.FFTPV.EncodedSelector.encoded_node_call,
      `RH080Next.FFTPV.MagnitudeIntoSource.magnitude_into_total,
      `RH080Next.FFTPV.AddMagnitudeSource.add_magnitude_total,
      `RH080Next.FFTPV.AddMagnitudeSource.result_conservation,
      `RH080Next.FFTPV.MultiplySmallSource.multiply_small_call_framed,
      `RH080Next.FFTPV.MultiplySmallSource.currentData_value,
      `RH080Next.FFTPV.StatusCall.assignment_every_execution,
      `RH080Next.FFTPV.RootSource.every_while_next,
      `GoldbachDirect.PureArgs.args_sound] do
    unless used.contains needed do throwError "Missing actual source/math quad dependency {needed}"
  logInfo m!"FFT_QUAD_AXIOMS {axioms}"
  logInfo "FFT_QUAD_AUDIT_PASS two-original-recursive-C-sources exact400and2520inputs actual-seven-statement-row whole-loop every-execution source-selector-to-existing-integer-quad Fap-extra100 W4-unscaled no-wrap real-memory caller-frame Std3 main-ANT-connection-pending"
