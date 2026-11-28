/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFullRangeApplications
import IEANTN.Nodes.CMSExplicitInputs.v1.Conclusions
import IEANTN.Nodes.CMSZeroSummation.v1.Conclusions
import IEANTN.Nodes.W4FourierNorm.v1.Conclusions
import IEANTN.Nodes.RHGlobalAffineIntervals.v1.Conclusions
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
open Real
namespace RHGlobalAffineIntervals.v1

/-- The declared zero-rule and norm supporting nodes are passed as actual
proof arguments, preserving the normal network's conditional edge. -/
theorem challenge_global_0851062
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hGap : CMSExplicitInputs.v1.historical_finite_gap)
    (hNorm : W4FourierNorm.v1.l1_bound)
    (hRH : RiemannHypothesis) : global_0851062 := by
  intro x hx
  exact RH080Next.ExplicitProfiles.w4_global_full_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hGap hNorm x hx

theorem challenge_branch_0777
    (h : RHFiniteAffineIntervals.v2.interval_0777_small) : branch_0777 := h

theorem challenge_branch_074
    (h : RHFiniteAffineIntervals.v2.interval_074_full) : branch_074 := h

theorem challenge_branch_075
    (h : RHFiniteAffineIntervals.v2.interval_075_full) : branch_075 := by
  intro x hx hxUpper
  have he : (11:ℝ)<exp 63 := by linarith [Real.add_one_le_exp (63:ℝ)]
  exact h x (by linarith) hxUpper

theorem challenge_branch_08
    (h : RHFiniteAffineIntervals.v2.interval_08_full) : branch_08 := by
  intro x hx hxUpper
  have he : (4:ℝ)<exp 70 := by linarith [Real.add_one_le_exp (70:ℝ)]
  exact h x (by linarith) hxUpper

theorem challenge_branch_0851062 (h : global_0851062) : branch_0851062 := by
  intro x hx
  have he : (4:ℝ)<exp 174 := by linarith [Real.add_one_le_exp (174:ℝ)]
  exact h x (by linarith)

/-- All five exact real branches, including equality at the three exponential
cutoffs. Every supporting branch proposition is genuinely consumed. -/
theorem challenge_piecewise_strict
    (hSmall : branch_0777) (h074 : branch_074) (h075 : branch_075)
    (h08 : branch_08) (hGlobal : branch_0851062) : piecewise_strict := by
  intro x hx
  by_cases hs : x<11
  · simpa only [piecewiseWidth,if_pos hs] using hSmall x hx hs
  by_cases h63 : x≤exp 63
  · simpa only [piecewiseWidth,if_neg hs,if_pos h63] using h074 x (by linarith) h63
  by_cases h70 : x≤exp 70
  · simpa only [piecewiseWidth,if_neg hs,if_neg h63,if_pos h70] using
      h075 x (lt_of_not_ge h63) h70
  by_cases h174 : x≤exp 174
  · simpa only [piecewiseWidth,if_neg hs,if_neg h63,if_neg h70,if_pos h174] using
      h08 x (lt_of_not_ge h70) h174
  · simpa only [piecewiseWidth,if_neg hs,if_neg h63,if_neg h70,if_neg h174] using
      hGlobal x (lt_of_not_ge h174)

#print axioms challenge_global_0851062
#print axioms challenge_branch_0777
#print axioms challenge_branch_074
#print axioms challenge_branch_075
#print axioms challenge_branch_08
#print axioms challenge_branch_0851062
#print axioms challenge_piecewise_strict
end RHGlobalAffineIntervals.v1
