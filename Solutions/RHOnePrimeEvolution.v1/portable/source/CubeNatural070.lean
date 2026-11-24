/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CubeDensity070
import UniformCubeNatural
namespace RHOnePrime.PowerPopulation
open Real Set
set_option maxHeartbeats 0

theorem cube_density_070_natural (hf : OcticFamily) {n : ℕ} (hn : 2981 ≤ n) :
    (7 / 10 : ℝ) * (n : ℝ) ^ 2 / log n <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) := by
  have hn' : (2981 : ℝ) ≤ n := by exact_mod_cast hn
  exact cube_density_070 hf (exp_eight_lt_2981.le.trans hn')

theorem cube_density_070_natural_from_sources
    (hGreen : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {n : ℕ} (hn : 2981 ≤ n) :
    (7 / 10 : ℝ) * (n : ℝ) ^ 2 / log n <
      ((QuarticWindow.primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ) :=
  cube_density_070_natural (RHOcticPush.OptimizedFinal.strict_count_family hGreen hN hB rh) hn

#print axioms cube_density_070_natural_from_sources
#check @cube_density_070_natural_from_sources
end RHOnePrime.PowerPopulation
