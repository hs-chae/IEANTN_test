/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.CMSFunctionalInput.v1.Conclusions
import IEANTN.Nodes.GaussianFourierWitness.v4.Conclusions
import IEANTN.Nodes.RHAsymptoticGaussian.v4.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import CMSPopulationFunctionalSource

noncomputable section
set_option autoImplicit false
open Real MeasureTheory Filter IEANTN.CMSFunctional
namespace RH080Next.Scaled40Canonical

theorem exact_bound_lt_readable : (20582561296/24680948495 : ℝ) <
    (833945313/1000000000 : ℝ) := by norm_num
theorem exact_bound_lt_v3 : (20582561296/24680948495 : ℝ)<
    (82325773717/98718416336 : ℝ) := by norm_num

theorem exact_bound_lt_v2 : (20582561296/24680948495 : ℝ) <
    (2746403660/3293251743 : ℝ) := by norm_num

theorem exact_bound_lt_v1 : (20582561296/24680948495 : ℝ) <
    (834021/1000000 : ℝ) := by norm_num
theorem exact_bound_lt_printed : (20582561296/24680948495 : ℝ) <
    (834050619151/1000000000000 : ℝ) := by norm_num

theorem eventual_lt_of_gap {c d : ℝ} (h : EventualGapBound c) (hcd : c < d) :
    ∀ᶠ n : ℕ in atTop, normalizedGap n < d := by
  have hev := h ((d-c)/2) (by linarith)
  filter_upwards [hev] with n hn
  linarith
end RH080Next.Scaled40Canonical

namespace RHAsymptoticGaussian.v4
open RHOnePrime.CMSFunctional RH080Next.Scaled40Canonical

/-- The actual objective-node input is consumed by the unchanged general CMS
source reduction. No particular Gaussian or bound occurs in that source input. -/
theorem challenge_normalized_gap (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) (hNumeric : GaussianFourierWitness.v4.objective_witness) :
    normalized_gap := by
  obtain ⟨F,G,hFG,hd,hq⟩ := hNumeric
  exact bound_mono (gap_from_functional hCMS hFG hd rh) hq

theorem challenge_gap_below_readable (hgap : normalized_gap) : gap_below_readable :=
  eventual_lt_of_gap hgap exact_bound_lt_readable

theorem challenge_gap_below_v3 (hgap : normalized_gap) : gap_below_v3 :=
  eventual_lt_of_gap hgap exact_bound_lt_v3

theorem challenge_gap_below_v2 (hgap : normalized_gap) : gap_below_v2 :=
  eventual_lt_of_gap hgap exact_bound_lt_v2

theorem challenge_gap_below_v1 (hgap : normalized_gap) : gap_below_v1 :=
  eventual_lt_of_gap hgap exact_bound_lt_v1

theorem challenge_gap_below_printed_2026 (hgap : normalized_gap) :
    gap_below_printed_2026 := eventual_lt_of_gap hgap exact_bound_lt_printed

theorem challenge_population_curve (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RH.v1.hypothesis) (hNumeric : GaussianFourierWitness.v4.objective_witness) :
    population_curve := by
  obtain ⟨F,G,hFG,hd,hq⟩ := hNumeric
  intro α hα ε hε
  apply population_from_functional hCMS hFG hd rh hα
  have hsum : 0 ≤ 1+2*α := by linarith
  have hm := mul_le_mul_of_nonneg_left hq hsum
  nlinarith

theorem challenge_population_count (hcurve : population_curve) : population_count := by
  intro α hα ε hε
  exact eventual_count_of_good (hcurve α hα ε hε)

#print axioms challenge_normalized_gap
#print axioms challenge_gap_below_readable
#print axioms challenge_gap_below_v3
#print axioms challenge_gap_below_v2
#print axioms challenge_gap_below_v1
#print axioms challenge_gap_below_printed_2026
#print axioms challenge_population_curve
#print axioms challenge_population_count
end RHAsymptoticGaussian.v4
