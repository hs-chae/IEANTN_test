/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PowerError
import IEANTN.Vocabulary.PrimeGaps
import IEANTN.Nodes.CH2.v6.Tables
import IEANTN.Nodes.FKS2.v2.Conclusions

namespace QRHPropagation.v2
open Real IEANTN

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def theta_frontier : Prop :=
  ∀ L C : ℝ, (L, C) ∈ CH2.v6.densityFrontier →
    HasPowerLogBound Eθ (C + 1 / 100000) 0 (7 / 8) (exp L)

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def pi_density_300 : Prop :=
  HasPowerLogBound Eπ 0.01323 0 (7 / 8) (exp 300)

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def prime_intervals_192 : Prop :=
  ∀ x ≥ exp 192, HasPrimeInInterval x (0.0345 * x ^ (7 / 8 : ℝ))

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def prime_intervals_300 : Prop :=
  ∀ x ≥ exp 300, HasPrimeInInterval x (0.0264 * x ^ (7 / 8 : ℝ))

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def classical_three : Prop :=
  HasClassicalBound Eψ 0.00000003 2 2 1 (exp 300) ∧
    HasClassicalBound Eθ 0.00000003 2 2 1 (exp 300) ∧
    HasClassicalBound Eπ 0.00000003 2 2 1 (exp 300)

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def mu_300 : Prop :=
  FKS2.v2.muAsymp 0.0000001 2 2 1 (exp 300) (exp 300) ≤ 0.6

end QRHPropagation.v2
