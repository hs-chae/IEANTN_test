/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.GaussianFourierWitness.v2.Conclusions
import Primal80Eligibility

noncomputable section
set_option autoImplicit false
open Real MeasureTheory IEANTN.CMSFunctional
namespace GaussianFourierWitness.v2

/-- The actual new 81-position polynomial pair and its closed integral
certificates provide the raw witness; there is no numerical-bound premise. -/
theorem challenge_integral_fourier_witness : integral_fourier_witness := by
  refine ⟨RH080.Gaussian40.physicalF,RH080.Gaussian40.physicalG,
    RH080.Primal80Gap.gaussian_eligible,?_,?_,RH080.Gaussian40.physicalF_zero_lower⟩
  · exact RH080.Gaussian40.physical_norm_upper
  · exact RH080.Gaussian40.physical_full_wings_upper

#print axioms challenge_integral_fourier_witness
end GaussianFourierWitness.v2
