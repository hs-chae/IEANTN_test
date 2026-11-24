/- Independent final-canonical audit: exact types, transitive axioms, proof-value
providers, and actual node-input use. This is kernel proof checking, not PV. -/
import Lean
import OnePrimeNetwork
import PowerPopulationSolution
import GoldbachV3Solution
import PrimeQuantileV4Solution

open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString, b.hasLooseBVar 0) :: leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []

run_cmd do
  let env ← getEnv
  let targets := #[
    (`RHOnePrimeEvolution.v1.challenge_kernel_ratio_lower, `RHOnePrime.CMSSharper.actual_cmsJ_sharper, #[]),
    (`RHOnePrimeEvolution.v1.closed_from_numeric, `RHOnePrime.CMSSharper.logarithmic_room, #["hCMS", "rh", "hJ"]),
    (`RHOnePrimeEvolution.v1.challenge_late_open_08768, `RHOnePrimeEvolution.v1.closed_from_numeric, #["hCMS", "rh", "hJ"]),
    (`RHOnePrimeEvolution.v1.challenge_uniform_open_08768, `RHOnePrime.FiniteGap.finite_coefficient_0004, #["hlate", "hgap"]),
    (`RHOnePrimeEvolution.v1.challenge_finite_slab_open_08301, `RHOnePrime.CMSOpen.open_prime_08301, #["hCMS", "rh"]),
    (`RHOnePrimeEvolution.v1.challenge_finite_absolute_1551, `RHOnePrime.FiniteGap.finite_constant_window, #["hgap"]),
    (`RHOnePrimeEvolution.v1.challenge_consecutive_gap_08768, `Nat.lt_of_not_ge, #["hi"]),
    (`RHOnePrimeEvolution.v1.challenge_continuous_late, `RHOnePrime.CMSContinuous.open_prime_continuous, #["hCMS", "rh"]),
    (`RHOnePrimeEvolution.v1.challenge_continuous_improves_uniform, `RHOnePrime.CMSContinuous.continuous_endpoint_lt_uniform, #[]),
    (`RHOnePrimeEvolution.v1.challenge_continuous_uniform, `RHOnePrime.FiniteGap.finite_constant_window, #["hlate", "hgap"]),
    (`RHOnePrimeEvolution.v1.challenge_bounded_open_08357, `RHOnePrime.CMSFinite.open_prime_08357, #["hCMS", "rh", "hgap"]),
    (`RHOnePrimeEvolution.v1.challenge_bounded_open_08512, `RHOnePrime.CMSFinite.open_prime_08512, #["hCMS", "rh", "hgap"]),
    (`RHOnePrimeEvolution.v1.challenge_bounded_open_08185, `RHOnePrime.CMSTight.open_prime_08185, #["hCMS", "rh", "hgap"]),
    (`PrimePowerPopulation.v1.challenge_cube_population_all_real, `RHOnePrime.PowerPopulation.cube_population, #["h"]),
    (`PrimePowerPopulation.v1.challenge_cube_density_all_real, `RHOnePrime.PowerPopulation.cube_density_070, #["h"]),
    (`PrimePowerPopulation.v1.challenge_cube_density_natural, `RHOnePrime.PowerPopulation.cube_density_070_natural, #["h"]),
    (`PrimePowerPopulation.v1.challenge_higher_power_population, `RHOnePrime.PowerPopulation.higher_power_population, #["h"]),
    (`PrimePowerPopulation.v1.challenge_cube_frontier, `RHOnePrime.PowerPopulation.cube_population_frontier_070, #["h"]),
    (`PrimePowerPopulation.v1.challenge_density_improves_648, `RHOnePrime.PowerPopulation.density_070_improves_648, #[]),
    (`Goldbach.v3.challenge_sorted_count_extended, `RHOnePrime.Canonical.extended_from_family, #["hi"]),
    (`Goldbach.v3.challenge_sorted_count_full_finite_range, `RHOnePrime.Canonical.full_range_from_family, #["hi"]),
    (`Goldbach.v3.challenge_sorted_count_750m_band, `RHOnePrime.Canonical.numeric_band_from_family, #["hi"]),
    (`PrimeQuantile.v4.challenge_strict_generic_block, `RHOnePrime.Canonical.generic_block_from_family, #["hi"]),
    (`PrimeQuantile.v4.challenge_strict_special_block, `RHOnePrime.Frontier.quantile_open_of_card, #["hi"]),
    (`PrimeQuantile.v4.challenge_shifted_sqrt_block, `RHOnePrime.Canonical.shifted_block_from_family, #["hi"])]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (root, expected, required) in targets do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard transitive axiom {root}: {axs}"
    let constants := info.value.getUsedConstants
    unless constants.contains expected do throwError "Expected proof-value provider missing {root}->{expected}"
    let uses := leadingUses info.value
    for parameter in required do
      unless uses.any (fun p => p.1 == parameter && p.2) do
        throwError "Required node input not consumed {root}:{parameter}; actual uses {uses}"
    logInfo m!"INDEPENDENT_CANONICAL_AUDIT {Json.mkObj [
      ("root", toJson root.toString), ("expected_provider", toJson expected.toString),
      ("axioms", toJson (axs.map Name.toString)),
      ("leading_parameters", toJson (uses.map fun (n, used) => Json.mkObj [
        ("name", toJson n), ("used_in_value", toJson used)])),
      ("value_constants", toJson (constants.map Name.toString))]}"
  logInfo m!"INDEPENDENT_CANONICAL_AUDIT_PASS {targets.size}"

/- These exact contracts independently pin every arrow in the canonical adapters. -/
example : RHOnePrimeEvolution.v1.kernel_ratio_lower := RHOnePrimeEvolution.v1.challenge_kernel_ratio_lower
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → RHOnePrimeEvolution.v1.kernel_ratio_lower → RHOnePrimeEvolution.v1.late_open_08768 := RHOnePrimeEvolution.v1.challenge_late_open_08768
example : RHOnePrimeEvolution.v1.late_open_08768 → PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.uniform_open_08768 := RHOnePrimeEvolution.v1.challenge_uniform_open_08768
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → RHOnePrimeEvolution.v1.finite_slab_open_08301 := RHOnePrimeEvolution.v1.challenge_finite_slab_open_08301
example : PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.finite_absolute_1551 := RHOnePrimeEvolution.v1.challenge_finite_absolute_1551
example : RHOnePrimeEvolution.v1.uniform_open_08768 → RHOnePrimeEvolution.v1.consecutive_gap_08768 := RHOnePrimeEvolution.v1.challenge_consecutive_gap_08768
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → RHOnePrimeEvolution.v1.continuous_late := RHOnePrimeEvolution.v1.challenge_continuous_late
example : RHOnePrimeEvolution.v1.continuous_improves_uniform := RHOnePrimeEvolution.v1.challenge_continuous_improves_uniform
example : RHOnePrimeEvolution.v1.continuous_late → PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.continuous_uniform := RHOnePrimeEvolution.v1.challenge_continuous_uniform
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.bounded_open_08357 := RHOnePrimeEvolution.v1.challenge_bounded_open_08357
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.bounded_open_08512 := RHOnePrimeEvolution.v1.challenge_bounded_open_08512
example : CMSCosineInput.v1.obstruction → RH.v1.hypothesis → PrimeGapTable.v1.gaps → RHOnePrimeEvolution.v1.bounded_open_08185 := RHOnePrimeEvolution.v1.challenge_bounded_open_08185
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v1.cube_population_all_real := PrimePowerPopulation.v1.challenge_cube_population_all_real
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v1.cube_density_all_real := PrimePowerPopulation.v1.challenge_cube_density_all_real
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v1.cube_density_natural := PrimePowerPopulation.v1.challenge_cube_density_natural
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v1.higher_power_population := PrimePowerPopulation.v1.challenge_higher_power_population
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v1.cube_frontier := PrimePowerPopulation.v1.challenge_cube_frontier
example : PrimePowerPopulation.v1.density_improves_648 := PrimePowerPopulation.v1.challenge_density_improves_648
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_extended := Goldbach.v3.challenge_sorted_count_extended
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_full_finite_range := Goldbach.v3.challenge_sorted_count_full_finite_range
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_750m_band := Goldbach.v3.challenge_sorted_count_750m_band
example : PrimeInterval.v4.optimized_strict_family → PrimeQuantile.v4.strict_generic_block := PrimeQuantile.v4.challenge_strict_generic_block
example : PrimeInterval.v4.optimized_strict_215 → PrimeQuantile.v4.strict_special_block := PrimeQuantile.v4.challenge_strict_special_block
example : PrimeInterval.v4.optimized_strict_family → PrimeQuantile.v4.shifted_sqrt_block := PrimeQuantile.v4.challenge_shifted_sqrt_block

/- Explicit mathematical identities pin endpoints, source boundary and constants. -/
open Real Set IEANTN.RHOnePrimeEvolution
example : CMSCosineInput.v1.obstruction = (RiemannHypothesis → ∀ L c : ℝ, 44 ≤ L → c ∈ Icc (1/2:ℝ) 1 → ¬ (∃ p : ℕ, p.Prime ∧ exp L ≤ (p:ℝ) ∧ (p:ℝ) ≤ exp L + c * sqrt (exp L) * L) → cmsJ * cmsMainScale c L ≤ cmsLogScale c L + 29/25) := rfl
example : PrimeGapTable.v1.gaps = (∀ p q : ℕ, p.Prime → q.Prime → p < q → q < 2^64 → (∀ r : ℕ, p < r → r < q → ¬r.Prime) → q-p ≤ 1550) := rfl
example : RHOnePrimeEvolution.v1.late_open_08768 = (∀ x : ℝ, exp 44 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(548/625)*sqrt x*log x) := rfl
example : RHOnePrimeEvolution.v1.uniform_open_08768 = (∀ x : ℝ, exp 24 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(548/625)*sqrt x*log x) := rfl
example : RHOnePrimeEvolution.v1.bounded_open_08357 = (∀ x : ℝ, exp 24 ≤ x → x ≤ exp 110 → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(8357/10000)*sqrt x*log x) := rfl
example : RHOnePrimeEvolution.v1.bounded_open_08512 = (∀ x : ℝ, exp 24 ≤ x → x ≤ exp 225 → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(532/625)*sqrt x*log x) := rfl
example : RHOnePrimeEvolution.v1.bounded_open_08185 = (∀ x : ℝ, exp 24 ≤ x → x ≤ exp 59 → ∃ p : ℕ, p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(1637/2000)*sqrt x*log x) := rfl
example : continuousEndpoint = (fun x : ℝ => x+2+coefficient (Real.log (x+1))*sqrt (x+1)*Real.log (x+1)) := rfl
