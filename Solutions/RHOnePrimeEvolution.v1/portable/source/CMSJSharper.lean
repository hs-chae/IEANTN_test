/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSKernelNumerics

/-! Recover unused rational slack in the already proved numerical bounds.
This is not a new test function or a novelty claim about the original source. -/
namespace RHOnePrime.CMSSharper
open Real
open RHOnePrimeEvolution.CMSNumerics

/-- Exact rational consequence of the actual proved integral and numerator. -/
theorem actual_cmsJ_sharper : (28517 / 25000 : ℝ) ≤ cmsJ := by
  have hSi := sine_integral_pos
  unfold cmsJ
  apply (le_div_iff₀ (by positivity :
    0 < (9 / 20 : ℝ) * ∫ x in (0 : ℝ)..π, sinc x)).mpr
  linarith [sine_integral_upper, cosine_kernel_numerator_lower]

#print axioms actual_cmsJ_sharper
end RHOnePrime.CMSSharper
