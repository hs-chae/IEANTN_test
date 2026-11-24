/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.PrimePowerPopulation.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v4.Conclusions
import CubeNatural070
import HigherPowerPopulation
namespace PrimePowerPopulation.v1
open Real

private theorem inherited_family (h : PrimeInterval.v4.optimized_strict_family) :
    RHOnePrime.PowerPopulation.OcticFamily := by
  simpa only [PrimeInterval.v4.optimized_strict_family, RHOnePrime.PowerPopulation.OcticFamily,
    QuarticWindow.primesBetween, IEANTN.PrimeWindows.primesBetween] using h

theorem challenge_cube_population_all_real
    (h : PrimeInterval.v4.optimized_strict_family) : cube_population_all_real := by
  intro n hn
  exact RHOnePrime.PowerPopulation.cube_population (inherited_family h) hn

theorem challenge_cube_density_all_real
    (h : PrimeInterval.v4.optimized_strict_family) : cube_density_all_real := by
  intro n hn
  exact RHOnePrime.PowerPopulation.cube_density_070 (inherited_family h) hn

theorem challenge_cube_density_natural
    (h : PrimeInterval.v4.optimized_strict_family) : cube_density_natural := by
  intro n hn
  exact RHOnePrime.PowerPopulation.cube_density_070_natural (inherited_family h) hn

theorem challenge_higher_power_population
    (h : PrimeInterval.v4.optimized_strict_family) : higher_power_population := by
  intro n hn r hr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r = k + 3 := ⟨r - 3, by omega⟩
  subst r
  simpa only [Nat.cast_add, Nat.cast_ofNat, QuarticWindow.primesBetween,
    IEANTN.PrimeWindows.primesBetween] using
    RHOnePrime.PowerPopulation.higher_power_population (inherited_family h) hn k

theorem challenge_cube_frontier
    (h : PrimeInterval.v4.optimized_strict_family) : cube_frontier := by
  intro n hn
  exact RHOnePrime.PowerPopulation.cube_population_frontier_070 (inherited_family h) hn

theorem challenge_density_improves_648 : density_improves_648 := by
  intro n hn
  exact RHOnePrime.PowerPopulation.density_070_improves_648 hn

#print axioms challenge_cube_population_all_real
#print axioms challenge_cube_density_all_real
#print axioms challenge_cube_density_natural
#print axioms challenge_higher_power_population
#print axioms challenge_cube_frontier
#print axioms challenge_density_improves_648
end PrimePowerPopulation.v1
