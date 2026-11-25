/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional
import Primal56ActualFourier

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory IEANTN.CMSFunctional
namespace RH080.Primal56Gap

theorem physicalF_zero_eq_one : RH080.Gaussian28.physicalF 0 = (1 : ℝ) := by
  norm_num [RH080.Gaussian28.physicalF, RH080.Gaussian28.normSource, RH080.Gaussian40.coeffEval]

/-- Actual G28 functions satisfy every CMS eligibility condition, including
the genuine Fourier identity and finite positive exterior leakage. -/
theorem gaussian_eligible : Eligible RH080.Gaussian28.physicalF RH080.Gaussian28.physicalG where
  continuous := RH080.Primal56Fourier.continuous_physicalF
  even := RH080.Primal56Fourier.physicalF_even
  integrable := RH080.Primal56Fourier.integrable_physicalF
  nonzero := by
    intro h
    have hz := congrFun h 0
    simp only [Pi.zero_apply] at hz
    rw [physicalF_zero_eq_one] at hz
    norm_num at hz
  fourier := RH080.Primal56Fourier.fourier_actual_physical
  leakage_integrable := by
    simpa only [max_comm] using
      RH080.Primal56Fourier.integrable_physicalG.pos_part.integrableOn

#print axioms gaussian_eligible
end RH080.Primal56Gap
