/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapSourceInterfaces
import IEANTN.Nodes.FapFourierNorm.v1.Conclusions
import IEANTN.Nodes.RHFiniteAffineIntervals.v1.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import ExplicitFullRangeApplications

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace RH080Next.Primal.FiniteCanonical

/-- Complete original real finite range, with strict prime endpoints.
The norm provider and every source/RH/finite-computation input are explicit. -/
theorem solution_interval_08_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v1.interval_08_full := by
  have hn : (∫ u : ℝ, |RH080Next.Explicit.inverseCosine
      (RH080Next.Explicit.affineSpectrum RH080Next.ExplicitProfiles.fapNodes 80) u|) ≤
      RH080Next.ExplicitProfiles.fapOriginalNormCap := by
    exact hNorm
  exact RH080Next.ExplicitProfiles.fap_08_full_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hGap hn

/-- Complete original real finite range, with strict prime endpoints.
The norm provider and every source/RH/finite-computation input are explicit. -/
theorem solution_interval_074_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v1.interval_074_full := by
  have hn : (∫ u : ℝ, |RH080Next.Explicit.inverseCosine
      (RH080Next.Explicit.affineSpectrum RH080Next.ExplicitProfiles.fapNodes 80) u|) ≤
      RH080Next.ExplicitProfiles.fapOriginalNormCap := by
    exact hNorm
  exact RH080Next.ExplicitProfiles.fap_074_full_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hGap hn

/-- Complete original real finite range, with strict prime endpoints.
The norm provider and every source/RH/finite-computation input are explicit. -/
theorem solution_interval_075_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) :
    RHFiniteAffineIntervals.v1.interval_075_full := by
  have hn : (∫ u : ℝ, |RH080Next.Explicit.inverseCosine
      (RH080Next.Explicit.affineSpectrum RH080Next.ExplicitProfiles.fapNodes 80) u|) ≤
      RH080Next.ExplicitProfiles.fapOriginalNormCap := by
    exact hNorm
  exact RH080Next.ExplicitProfiles.fap_075_full_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hGap hn

/-- The exact elementary prime5/7/11 proof, with no imported hypothesis. -/
theorem solution_interval_0777_small : RHFiniteAffineIntervals.v1.interval_0777_small :=
  RH080Next.FiniteGap.direct_small_0777

end RH080Next.Primal.FiniteCanonical

namespace RHFiniteAffineIntervals.v1

theorem challenge_interval_08_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_08_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_08_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

theorem challenge_interval_074_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_074_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_074_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

theorem challenge_interval_075_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSExplicitInputs.v1.zero_partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v1.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_075_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_075_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

theorem challenge_interval_0777_small : interval_0777_small :=
  RH080Next.Primal.FiniteCanonical.solution_interval_0777_small

end RHFiniteAffineIntervals.v1
