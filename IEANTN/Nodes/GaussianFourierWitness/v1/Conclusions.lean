import IEANTN.Vocabulary.CMSFunctional

namespace GaussianFourierWitness.v1
open IEANTN.CMSFunctional
/-- An actual even continuous real L1 Fourier pair with certified full mass,
full positive exterior leakage, and value at zero. The Solution supplies the
specific rational degree24 polynomial-Gaussian functions; core stays abstract. -/
def integral_fourier_witness : Prop := ∃ F G : ℝ → ℝ,
  Eligible F G ∧ mass F ≤ (74899/100000 : ℝ) ∧
    positiveLeak G ≤ (31152/1000000 : ℝ) ∧
      (999999999/1000000000 : ℝ) ≤ F 0
/-- The positivity and inverse-functional bound are derived from the preceding
raw integral witness by exact arithmetic, not supplied as an extra assumption. -/
def objective_witness : Prop := ∃ F G : ℝ → ℝ,
  Eligible F G ∧ 0 < denominator F G ∧
    inverseObjective F G ≤ (834021/1000000 : ℝ)
end GaussianFourierWitness.v1
