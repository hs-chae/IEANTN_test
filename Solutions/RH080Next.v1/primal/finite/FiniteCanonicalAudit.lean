/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FapNormNodeSolution
import FiniteIntervalsNodeSolution

namespace RH080Next.Primal.FiniteCanonical

/-- Complete canonical composition. The numerical norm is proved here,
not an additional premise. This is a kernel-only FFT provider, not C FFT PV. -/
theorem kernel_interval_08_full
    (hBR : BRFourierInput.v1.norm_identity)
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v1.interval_08_full :=
  RHFiniteAffineIntervals.v1.challenge_interval_08_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap
    (FapFourierNorm.v1.challenge_l1_bound hBR) hRH

/-- Complete canonical composition. The numerical norm is proved here,
not an additional premise. This is a kernel-only FFT provider, not C FFT PV. -/
theorem kernel_interval_074_full
    (hBR : BRFourierInput.v1.norm_identity)
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v1.interval_074_full :=
  RHFiniteAffineIntervals.v1.challenge_interval_074_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap
    (FapFourierNorm.v1.challenge_l1_bound hBR) hRH

/-- Complete canonical composition. The numerical norm is proved here,
not an additional premise. This is a kernel-only FFT provider, not C FFT PV. -/
theorem kernel_interval_075_full
    (hBR : BRFourierInput.v1.norm_identity)
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v1.interval_075_full :=
  RHFiniteAffineIntervals.v1.challenge_interval_075_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap
    (FapFourierNorm.v1.challenge_l1_bound hBR) hRH

end RH080Next.Primal.FiniteCanonical

open Lean Elab Command

private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

private partial def finiteApplicationClosure (env : Environment) : List Name → List Name → List Name
  | [], seen => seen
  | root::rest, seen =>
    if seen.contains root then finiteApplicationClosure env rest seen else
    let seen := root::seen
    if !(root.toString.startsWith "RH080Next." || root.toString.startsWith "RHOnePrime." ||
      root.toString.startsWith "FapForest17." || root.toString.startsWith "BRFourierInput." ||
      root.toString.startsWith "CMSExplicitInputs." || root.toString.startsWith "FapFourierNorm." ||
      root.toString.startsWith "RHFiniteAffineIntervals." || root.toString.startsWith "IEANTN." ||
      root.toString.startsWith "GoldbachDirect.") then finiteApplicationClosure env rest seen
    else match env.find? root with
      | none => finiteApplicationClosure env rest seen
      | some info =>
        let constants := info.type.getUsedConstants
        let constants := match info with
          | .thmInfo value => constants ++ value.value.getUsedConstants
          | .defnInfo value => constants ++ value.value.getUsedConstants
          | _ => constants
        finiteApplicationClosure env (constants.toList ++ rest) seen

example : BRFourierInput.v1.norm_identity → FapFourierNorm.v1.l1_bound :=
  FapFourierNorm.v1.challenge_l1_bound
example : RHFiniteAffineIntervals.v1.interval_0777_small :=
  RHFiniteAffineIntervals.v1.challenge_interval_0777_small

run_cmd do
  let env ← getEnv
  let roots := #[
    `FapFourierNorm.v1.challenge_l1_bound,
    `RHFiniteAffineIntervals.v1.challenge_interval_08_full,
    `RHFiniteAffineIntervals.v1.challenge_interval_074_full,
    `RHFiniteAffineIntervals.v1.challenge_interval_075_full,
    `RHFiniteAffineIntervals.v1.challenge_interval_0777_small,
    `RH080Next.Primal.FiniteCanonical.kernel_interval_08_full,
    `RH080Next.Primal.FiniteCanonical.kernel_interval_074_full,
    `RH080Next.Primal.FiniteCanonical.kernel_interval_075_full]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Unaccepted axiom {root}: {axioms}"
    logInfo m!"FINITE_CANONICAL_AXIOMS {root}: {axioms}"
    if root.toString.startsWith "RH080Next.Primal.FiniteCanonical.kernel_interval_" then
      for parameter in ["hBR","hStrip","hGW","hDigamma","hEta","hCount","hPartial","hMV","hGap","hRH"] do
        unless (leadingUses info.value).any (fun p => p.1 == parameter && p.2) do
          throwError "Source/RH input not consumed {root}:{parameter}"
  let all := finiteApplicationClosure env roots.toList []
  for required in #[
    `RH080Next.Primal.FapFFTKernel.kernel_actual_norm,
    `RH080Next.Primal.FapFFTKernel.kernel_periodic_norm,
    `FapForest17.complete_execution,
    `FapForest17.sample_error,
    `RH080Next.ExplicitProfiles.fap_08_full_of_norm,
    `RH080Next.ExplicitProfiles.fap_074_full_of_norm,
    `RH080Next.ExplicitProfiles.fap_075_full_of_norm,
    `RH080Next.FiniteGap.direct_small_0777] do
    unless all.contains required do throwError "Missing actual numerical/analytic dependency {required}"
  for name in all do
    if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" ||
       name.toString.startsWith "Lean.trustCompiler" || name.toString.startsWith "Lean.native" then
      throwError "Native/sorry dependency {name}"
  logInfo m!"FINITE_CANONICAL_AUDIT_PASS roots={roots.size} finiteApplicationClosure={all.length}; original_numerical_input_exact; norm_and_source_edges_consumed; KERNEL_ONLY_NOT_C_FFT_PV"
