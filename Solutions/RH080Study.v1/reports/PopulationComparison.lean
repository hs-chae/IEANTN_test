import Mathlib.Tactic

/-! Exact scalar comparison used by the population figure. This file is not
the Fourier-to-primes reduction and introduces no analytic input. -/
namespace RH080.PopulationComparison
noncomputable section

def q : ℝ := 82325773717 / 98718416336
def gaussianWidth (α : ℝ) : ℝ := q * (1 + 2 * α)
def octicLimitingWidth (α : ℝ) : ℝ := 163827 / 160000 + (9 / 8) * α
def crossing : ℝ := (163827 / 160000 - q) / (2 * q - 9 / 8)

theorem crossover (α : ℝ) :
    gaussianWidth α ≤ octicLimitingWidth α ↔ α ≤ crossing := by
  dsimp [gaussianWidth, octicLimitingWidth, crossing, q]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem crossover_range : (349 / 1000 : ℝ) < crossing ∧ crossing < (351 / 1000 : ℝ) := by
  norm_num [crossing, q]

theorem root_population_octic_shorter :
    octicLimitingWidth 1 < gaussianWidth 1 := by
  norm_num [octicLimitingWidth, gaussianWidth, q]

#print axioms crossover
#print axioms crossover_range
#print axioms root_population_octic_shorter
end
end RH080.PopulationComparison
