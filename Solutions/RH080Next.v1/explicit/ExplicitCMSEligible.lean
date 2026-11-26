/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFourierPair
import IEANTN.Vocabulary.CMSFunctional

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem integrable_positive_part (W : ℝ → ℝ) (hW : Integrable W) :
    Integrable (fun v : ℝ => max 0 (W v)) := by
  apply ((hW.add hW.abs).div_const 2).congr
  filter_upwards with v
  simp only [Pi.add_apply]
  by_cases hv : 0 ≤ W v
  · rw [max_eq_right hv, abs_of_nonneg hv]
    ring
  · rw [max_eq_left (le_of_not_ge hv), abs_of_neg (lt_of_not_ge hv)]
    ring

/-- The actual finite affine witness belongs to the pre-existing CMS source
class. No support size, Fourier equality, integrability, or nonzero-function
premise is hidden behind a numerical certificate. -/
theorem affine_inverse_eligible (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (hf0 : nodalF0 nodes m ≠ 0) :
    IEANTN.CMSFunctional.Eligible (inverseCosine (affineSpectrum nodes m))
      (affineSpectrum nodes m) := by
  have hW := integrable_affineSpectrum nodes m hlen hm
  refine ⟨continuous_inverseCosine _ hW, inverseCosine_even _,
    integrable_inverseCosine_affineSpectrum nodes m hlen hm hlast, ?_,
    fourier_affine_inverse_eq_window nodes m hlen hm hlast,
    (integrable_positive_part _ hW).integrableOn⟩
  intro hz
  apply hf0
  rw [← integral_affineSpectrum nodes m hm, ← inverseCosine_zero]
  exact congrFun hz 0

end RH080Next.Explicit
