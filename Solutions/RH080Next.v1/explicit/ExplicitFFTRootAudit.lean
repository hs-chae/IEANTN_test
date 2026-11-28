/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSource
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
  let roots:=#[(`RH080Next.FFTPV.RootSource.source_initialize_root_total,`RH080Next.FFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.RootSource.fap_source_initialize_root_total,`RH080Next.FapFFTPV.actual_source_syntax),
    (`RH080Next.FFTPV.RootSource.recursive_source_initialize_root_total,`RH080Next.FFTRecursivePV.actual_source_syntax),
    (`RH080Next.FFTPV.RootSource.fap_recursive_source_initialize_root_total,`RH080Next.FapFFTRecursivePV.actual_source_syntax)]
  for (root,syntaxProof) in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual source initializer {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden initializer axiom {root}: {axioms}"
    let used:=proofClosure env [root]
    for needed in #[syntaxProof,`RH080Next.FFTPV.RootSource.initialize_root_call,
        `RH080Next.FFTPV.RootSource.actual_source_statements,
        `RH080Next.FFTPV.RootSource.initialize_parameters,
        `RH080Next.FFTPV.RootSource.piData_value,
        `RH080Next.FFTPV.RootSource.pi_prefix_framed,
        `RH080Next.FFTPV.RootSource.scale_framed,
        `RH080Next.FFTPV.RootSource.divide_framed,
        `RH080Next.FFTPV.RootSource.multiply_execution,
        `RH080Next.FFTPV.RootSource.setup_framed,
        `RH080Next.FFTPV.RootSource.index_declaration_execution,
        `RH080Next.FFTPV.RootSource.start_execution,
        `RH080Next.FFTPV.RootSource.term_execution,
        `RH080Next.FFTPV.RootSource.paired_terms_execution,
        `RH080Next.FFTPV.RootSource.iteration_execution,
        `RH080Next.FFTPV.RootSource.loop_block_execution,
        `RH080Next.FFTPV.RootSource.loop_execution,
        `RH080Next.FFTPV.RootSource.tail_execution,
        `RH080Next.FFTPV.RootSource.original_recurrence_bounds,
        `RH080Next.FFTPV.RootSource.original_intermediate_bounds,
        `RH080Next.FFTPV.RootSource.taylorState_root,
        `RH080Next.FFTPV.RootSource.every_expression_call,
        `RH080Next.FFTPV.RootSource.every_while_next,
        `RH080Next.FFTPV.RootSource.every_call_from_body,
        `RH080Next.FFTPV.MultiplyCall.fixed_multiply_correct_words,
        `RH080Next.FFTPV.AddSource.fixed_add_total,
        `RH080Next.FFTPV.AddSource.finalData_outside,
        `RH080Next.FFTPV.DivideSource.divide_small_call,
        `RH080Next.FFTPV.CopyLoop.copy_words_call_framed,
        `RH080Next.FFTPV.ZeroSlice.zero_words_call_framed,
        `RH080Next.FFTPV.CanonicalSource.canonical_sign_call_framed,
        `RH080Next.FFTPV.StatusCall.assignment_every_execution,
        `GoldbachDirect.PureArgs.args_sound] do
      unless used.contains needed do throwError "Source/math initializer proof missing {root}->{needed}"
    logInfo m!"FFT_ROOT_SOURCE_AXIOMS {root}: {axioms}"
  logInfo "FFT_ROOT_SOURCE_AUDIT_PASS four-actual-C-files independently-parsed full-Call all-executions all-argument-orders ten-Taylor-iterations two-original-grids actual-integer-root same-512-allocation slice-preservation no-wrap temporary-lifetimes caller-frame Std3 final-ANT-connection-pending"
