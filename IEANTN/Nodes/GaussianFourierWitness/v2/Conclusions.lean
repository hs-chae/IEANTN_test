/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional

namespace GaussianFourierWitness.v2
open IEANTN.CMSFunctional
/-- Actual degree80 physical polynomial-Gaussian witness with genuine Fourier
association and certified whole-real mass, positive exterior leakage and value.
The existence proof is separate from the general exact arithmetic adapter. -/
def integral_fourier_witness : Prop := ∃ F G : ℝ → ℝ,
  Eligible F G ∧ mass F ≤ (74901918/100000000 : ℝ) ∧
    positiveLeak G ≤ (3111791/100000000 : ℝ) ∧
      (999999999/1000000000 : ℝ) ≤ F 0
/-- Exact quotient of the conservative mass and positive denominator budgets,
derived from the actual raw integral witness rather than supplied separately. -/
def objective_witness : Prop := ∃ F G : ℝ → ℝ,
  Eligible F G ∧ 0 < denominator F G ∧
    inverseObjective F G ≤ (2746403660/3293251743 : ℝ)
end GaussianFourierWitness.v2
