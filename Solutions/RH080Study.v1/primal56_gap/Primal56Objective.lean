/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.GaussianFourierWitness.v3.Conclusions
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open IEANTN.CMSFunctional
namespace GaussianFourierWitness.v3

/-- Every raw numerical input is consumed in positivity and exact division. -/
theorem challenge_objective_witness (hNumeric : integral_fourier_witness) :
    objective_witness := by
  obtain ⟨F,G,hFG,hmass,hleak,hzero⟩ := hNumeric
  have hd : 0 < denominator F G := by
    unfold denominator
    nlinarith
  refine ⟨F,G,hFG,hd,?_⟩
  unfold inverseObjective
  apply (div_le_iff₀ hd).mpr
  unfold denominator
  nlinarith

#print axioms challenge_objective_witness
end GaussianFourierWitness.v3
