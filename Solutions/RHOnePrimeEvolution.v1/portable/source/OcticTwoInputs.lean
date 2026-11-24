/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticPrimePowerScalars

namespace RHLimit.OcticTwoInputs
open Real Set
open RHLimit.OcticGeometry RHLimit.OcticPrimePowers

/-- Original fixed2.15 conclusion. Geometry, coverage, prime-power cost, and
trivial-zero cost are now theorems; the two analytic contracts remain explicit. -/
theorem prime_count_215 (rh : RiemannHypothesis)
    (hef : EvenKernel.ExplicitFormula 4 (43 / 20))
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125)) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  prime_count_215_three_inputs rh hef hz primepower_cost_215

/-- Original full real-parameter frontier; no new assumptions or weaker parameters. -/
theorem prime_count_family (rh : RiemannHypothesis)
    (hef : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.ExplicitFormula 4 C)
    (hz : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
      EvenKernel.ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20)) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, Real.exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + C * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u :=
  OcticConsumer.prime_count_family rh hef hz
    (fun _ hC => primepower_cost_family 4 hC)
    (fun _ hC => trivial_cost_family 4 hC)
    (fun _ hC => scalar_geometry_family hC)
    (fun _ hC => forward_coverage_family hC)

#print axioms prime_count_215
#print axioms prime_count_family
end RHLimit.OcticTwoInputs
