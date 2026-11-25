/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional
import G40Wings
import Primal80ActualFourier

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory IEANTN.CMSFunctional
namespace RH080.Primal80Gap

/-- Actual G40 functions satisfy every CMS eligibility condition, including
the genuine Fourier identity and finite positive exterior leakage. -/
theorem gaussian_eligible : Eligible RH080.Gaussian40.physicalF RH080.Gaussian40.physicalG where
  continuous := RH080.Primal80Fourier.continuous_physicalF
  even := RH080.Primal80Fourier.physicalF_even
  integrable := RH080.Primal80Fourier.integrable_physicalF
  nonzero := by
    intro h
    have hz := congrFun h 0
    simp only [Pi.zero_apply] at hz
    have hlo := RH080.Gaussian40.physicalF_zero_lower
    linarith
  fourier := RH080.Primal80Fourier.fourier_actual_physical
  leakage_integrable := by
    simpa only [max_comm] using
      RH080.Primal80Fourier.integrable_physicalG.pos_part.integrableOn

#print axioms gaussian_eligible
end RH080.Primal80Gap
