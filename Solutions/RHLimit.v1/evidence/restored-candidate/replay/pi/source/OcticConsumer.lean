/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import EvenKernel

namespace OcticConsumer
open Real Set

/-- The actual-prime-count coefficient2.15 consumer. Its source and geometric
contracts are explicit remaining obligations, not hidden RH consequences. -/
theorem prime_count_215 (rh : RiemannHypothesis)
    (hef : EvenKernel.ExplicitFormula 4 (43 / 20))
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125))
    (hpp : EvenKernel.PrimePowerCost 4 (43 / 20) (31 / 2000))
    (ht : EvenKernel.TrivialCost 4 (43 / 20) (1 / 1000))
    (hg : EvenKernel.ScalarGeometry 4 (43 / 20) (911 / 500) (3 / 2)
      (3 / 125) (31 / 2000) (1 / 1000) (29 / 5))
    (hc : EvenKernel.ForwardCoverage (43 / 20)) :
    ∀ u : ℝ, Real.exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + 43 / 20 * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u := by
  have h := EvenKernel.prime_count_from_kernel 4 (43 / 20) (911 / 500) (3 / 2)
    (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) rh hef hz hpp ht hg hc
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h ⊢
  exact h

/-- The full width/count frontier for every eligibleC, with a uniform finite
bonus. This is more information than a single interval-existence export. -/
theorem prime_count_family (rh : RiemannHypothesis)
    (hef : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.ExplicitFormula 4 C)
    (hz : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
      EvenKernel.ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20))
    (hpp : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.PrimePowerCost 4 C (29 / 500))
    (ht : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.TrivialCost 4 C (1 / 1000))
    (hg : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
      EvenKernel.ScalarGeometry 4 C (911 / 500) (3 / 2)
        (3 / 20) (29 / 500) (1 / 1000) (21 / 5))
    (hc : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.ForwardCoverage C) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, Real.exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + C * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u := by
  intro C hC
  have h := EvenKernel.prime_count_from_kernel 4 C (911 / 500) (3 / 2)
    (3 / 20) (29 / 500) (1 / 1000) (21 / 5) rh (hef C hC) (hz C hC)
      (hpp C hC) (ht C hC) (hg C hC) (hc C hC)
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  convert h using 1 <;> ring

#print axioms prime_count_215
#print axioms prime_count_family
end OcticConsumer
