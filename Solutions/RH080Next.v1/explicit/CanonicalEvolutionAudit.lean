/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalFiniteNodeSolution
import Lean
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option maxHeartbeats 0
open Lean Elab Command

-- Exact statement/data preservation, independent of any new source provider.
example : FapFourierNorm.v2.Tables.affineNodes = FapFourierNorm.v1.Tables.affineNodes := rfl
example : FapFourierNorm.v2.l1_bound = FapFourierNorm.v1.l1_bound := rfl
example : RHFiniteAffineIntervals.v2.interval_08_full = RHFiniteAffineIntervals.v1.interval_08_full := rfl
example : RHFiniteAffineIntervals.v2.interval_074_full = RHFiniteAffineIntervals.v1.interval_074_full := rfl
example : RHFiniteAffineIntervals.v2.interval_075_full = RHFiniteAffineIntervals.v1.interval_075_full := rfl
example : RHFiniteAffineIntervals.v2.interval_0777_small = RHFiniteAffineIntervals.v1.interval_0777_small := rfl
example : CMSZeroSummation.v1.partial_summation = CMSExplicitInputs.v1.zero_partial_summation := rfl

example : CMSZeroSummation.v1.partial_summation := CMSZeroSummation.v1.challenge_partial_summation

example
    (brfourierinput_v1_norm_identity : BRFourierInput.v1.norm_identity) :
    FapFourierNorm.v2.l1_bound := FapFourierNorm.v2.challenge_l1_bound brfourierinput_v1_norm_identity

example
    (cmsexplicitinputs_v1_strip_regularity : CMSExplicitInputs.v1.strip_regularity)
    (cmsexplicitinputs_v1_guinand_weil : CMSExplicitInputs.v1.guinand_weil)
    (cmsexplicitinputs_v1_digamma_integral : CMSExplicitInputs.v1.digamma_integral)
    (cmsexplicitinputs_v1_real_eta_integral : CMSExplicitInputs.v1.real_eta_integral)
    (cmsexplicitinputs_v1_zero_counting : CMSExplicitInputs.v1.zero_counting)
    (cmszerosummation_v1_partial_summation : CMSZeroSummation.v1.partial_summation)
    (cmsexplicitinputs_v1_montgomery_vaughan : CMSExplicitInputs.v1.montgomery_vaughan)
    (cmsexplicitinputs_v1_historical_finite_gap : CMSExplicitInputs.v1.historical_finite_gap)
    (fapfouriernorm_v2_l1_bound : FapFourierNorm.v2.l1_bound)
    (rh_v1_hypothesis : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v2.interval_08_full := RHFiniteAffineIntervals.v2.challenge_interval_08_full cmsexplicitinputs_v1_strip_regularity cmsexplicitinputs_v1_guinand_weil cmsexplicitinputs_v1_digamma_integral cmsexplicitinputs_v1_real_eta_integral cmsexplicitinputs_v1_zero_counting cmszerosummation_v1_partial_summation cmsexplicitinputs_v1_montgomery_vaughan cmsexplicitinputs_v1_historical_finite_gap fapfouriernorm_v2_l1_bound rh_v1_hypothesis

example
    (cmsexplicitinputs_v1_strip_regularity : CMSExplicitInputs.v1.strip_regularity)
    (cmsexplicitinputs_v1_guinand_weil : CMSExplicitInputs.v1.guinand_weil)
    (cmsexplicitinputs_v1_digamma_integral : CMSExplicitInputs.v1.digamma_integral)
    (cmsexplicitinputs_v1_real_eta_integral : CMSExplicitInputs.v1.real_eta_integral)
    (cmsexplicitinputs_v1_zero_counting : CMSExplicitInputs.v1.zero_counting)
    (cmszerosummation_v1_partial_summation : CMSZeroSummation.v1.partial_summation)
    (cmsexplicitinputs_v1_montgomery_vaughan : CMSExplicitInputs.v1.montgomery_vaughan)
    (cmsexplicitinputs_v1_historical_finite_gap : CMSExplicitInputs.v1.historical_finite_gap)
    (fapfouriernorm_v2_l1_bound : FapFourierNorm.v2.l1_bound)
    (rh_v1_hypothesis : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v2.interval_074_full := RHFiniteAffineIntervals.v2.challenge_interval_074_full cmsexplicitinputs_v1_strip_regularity cmsexplicitinputs_v1_guinand_weil cmsexplicitinputs_v1_digamma_integral cmsexplicitinputs_v1_real_eta_integral cmsexplicitinputs_v1_zero_counting cmszerosummation_v1_partial_summation cmsexplicitinputs_v1_montgomery_vaughan cmsexplicitinputs_v1_historical_finite_gap fapfouriernorm_v2_l1_bound rh_v1_hypothesis

example
    (cmsexplicitinputs_v1_strip_regularity : CMSExplicitInputs.v1.strip_regularity)
    (cmsexplicitinputs_v1_guinand_weil : CMSExplicitInputs.v1.guinand_weil)
    (cmsexplicitinputs_v1_digamma_integral : CMSExplicitInputs.v1.digamma_integral)
    (cmsexplicitinputs_v1_real_eta_integral : CMSExplicitInputs.v1.real_eta_integral)
    (cmsexplicitinputs_v1_zero_counting : CMSExplicitInputs.v1.zero_counting)
    (cmszerosummation_v1_partial_summation : CMSZeroSummation.v1.partial_summation)
    (cmsexplicitinputs_v1_montgomery_vaughan : CMSExplicitInputs.v1.montgomery_vaughan)
    (cmsexplicitinputs_v1_historical_finite_gap : CMSExplicitInputs.v1.historical_finite_gap)
    (fapfouriernorm_v2_l1_bound : FapFourierNorm.v2.l1_bound)
    (rh_v1_hypothesis : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v2.interval_075_full := RHFiniteAffineIntervals.v2.challenge_interval_075_full cmsexplicitinputs_v1_strip_regularity cmsexplicitinputs_v1_guinand_weil cmsexplicitinputs_v1_digamma_integral cmsexplicitinputs_v1_real_eta_integral cmsexplicitinputs_v1_zero_counting cmszerosummation_v1_partial_summation cmsexplicitinputs_v1_montgomery_vaughan cmsexplicitinputs_v1_historical_finite_gap fapfouriernorm_v2_l1_bound rh_v1_hypothesis

example : RHFiniteAffineIntervals.v2.interval_0777_small := RHFiniteAffineIntervals.v2.challenge_interval_0777_small

private def conjugationProofValue? : ConstantInfo → Option Expr
  | .thmInfo info=>some info.value
  | .defnInfo info=>some info.value
  | _=>none
private partial def conjugationProofClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | []=>seen
  | n::rest=>if seen.contains n then conjugationProofClosure env rest seen else
    let seen:=seen.insert n
    match env.find? n with
    | some info=>match conjugationProofValue? info with
      | some body=>conjugationProofClosure env (body.getUsedConstants.toList++rest) seen
      | none=>conjugationProofClosure env rest seen
    | none=>conjugationProofClosure env rest seen
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let roots := #[
    `CMSZeroSummation.v1.challenge_partial_summation,
    `FapFourierNorm.v2.challenge_l1_bound,
    `RHFiniteAffineIntervals.v2.challenge_interval_08_full,
    `RHFiniteAffineIntervals.v2.challenge_interval_074_full,
    `RHFiniteAffineIntervals.v2.challenge_interval_075_full,
    `RHFiniteAffineIntervals.v2.challenge_interval_0777_small,
    `RH080Next.CanonicalEvolution.source_first_interval_08_full,
    `RH080Next.CanonicalEvolution.source_first_interval_074_full,
    `RH080Next.CanonicalEvolution.source_first_interval_075_full]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing canonical theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Nonstandard canonical axiom {root}: {axioms}"
    logInfo m!"CANONICAL_EVOLUTION_AXIOMS {root}: {axioms}"
  let sourceRoots := #[`FapFourierNorm.v2.challenge_l1_bound,
    `RH080Next.CanonicalEvolution.source_first_interval_08_full,
    `RH080Next.CanonicalEvolution.source_first_interval_074_full,
    `RH080Next.CanonicalEvolution.source_first_interval_075_full]
  for root in sourceRoots do
    let used := conjugationProofClosure env [root]
    unless used.contains `RH080Next.FFTPV.FapMain.source_first_actual_norm do
      throwError "Actual C norm provider not consumed by {root}"
    unless used.contains `RH080Next.FFTPV.FapMain.actual_main_result do
      throwError "Actual source execution output not consumed by {root}"
    for required in #[`RH080Next.FFTPV.MainIO.actual_main_success,
      `RH080Next.FFTPV.MainIO.every_main_call,`RH080Next.FFTPV.MainIO.result_value_eq,
      `RH080Next.FFTPV.MainIO.source_main_call,`RH080Next.FFTPV.MainIO.every_printf_arguments,
      `RH080Next.FFTPV.MainIO.actual_result] do
      unless used.contains required do throwError "Full operational main/printf path missing {root}: {required}"
  for root in sourceRoots.toList.tail do
    let used := conjugationProofClosure env [root]
    unless used.contains `RH080Next.Explicit.cms_zero_partial_summation_kernel do
      throwError "Kernel zero theorem not consumed by {root}"
  logInfo "CANONICAL_EVOLUTION_AUDIT_PASS roots=9 six-exact-generated-interfaces three-full-network-compositions original-Fap-data-and-claims source-first-full-main-printf-C-norm kernel-zero-rule Std3 no-native"
