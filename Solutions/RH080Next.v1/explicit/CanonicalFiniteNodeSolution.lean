/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalZeroNodeSolution
import CanonicalFapNormNodeSolution
import FiniteIntervalsNodeSolution
import IEANTN.Nodes.RHFiniteAffineIntervals.v2.Conclusions
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace RHFiniteAffineIntervals.v2

/-- Same original strict finite-range conclusion. The new graph's zero and
norm supporting propositions are both consumed as actual proof arguments. -/
theorem challenge_interval_08_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v2.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_08_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_08_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

/-- Same original strict finite-range conclusion. The new graph's zero and
norm supporting propositions are both consumed as actual proof arguments. -/
theorem challenge_interval_074_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v2.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_074_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_074_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

/-- Same original strict finite-range conclusion. The new graph's zero and
norm supporting propositions are both consumed as actual proof arguments. -/
theorem challenge_interval_075_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : FapFourierNorm.v2.l1_bound)
    (hRH : RH.v1.hypothesis) : interval_075_full :=
  RH080Next.Primal.FiniteCanonical.solution_interval_075_full
    hStrip hGW hDigamma hEta hCount hPartial hMV hGap hNorm hRH

theorem challenge_interval_0777_small : interval_0777_small :=
  RH080Next.Primal.FiniteCanonical.solution_interval_0777_small
end RHFiniteAffineIntervals.v2

namespace RH080Next.CanonicalEvolution

/-- Full network composition: no numerical norm or generic zero-rule premise
remains; the two new proved supporting nodes supply those exact inputs. -/
theorem source_first_interval_08_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hBR : BRFourierInput.v1.norm_identity)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v2.interval_08_full :=
  RHFiniteAffineIntervals.v2.challenge_interval_08_full
    hStrip hGW hDigamma hEta hCount
    CMSZeroSummation.v1.challenge_partial_summation hMV hGap
    (FapFourierNorm.v2.challenge_l1_bound hBR) hRH

/-- Full network composition: no numerical norm or generic zero-rule premise
remains; the two new proved supporting nodes supply those exact inputs. -/
theorem source_first_interval_074_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hBR : BRFourierInput.v1.norm_identity)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v2.interval_074_full :=
  RHFiniteAffineIntervals.v2.challenge_interval_074_full
    hStrip hGW hDigamma hEta hCount
    CMSZeroSummation.v1.challenge_partial_summation hMV hGap
    (FapFourierNorm.v2.challenge_l1_bound hBR) hRH

/-- Full network composition: no numerical norm or generic zero-rule premise
remains; the two new proved supporting nodes supply those exact inputs. -/
theorem source_first_interval_075_full
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hBR : BRFourierInput.v1.norm_identity)
    (hRH : RH.v1.hypothesis) : RHFiniteAffineIntervals.v2.interval_075_full :=
  RHFiniteAffineIntervals.v2.challenge_interval_075_full
    hStrip hGW hDigamma hEta hCount
    CMSZeroSummation.v1.challenge_partial_summation hMV hGap
    (FapFourierNorm.v2.challenge_l1_bound hBR) hRH

end RH080Next.CanonicalEvolution
