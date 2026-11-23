/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeQuantile.v1
open Real
/-- Every consecutive prime index below the full lower count is located in the new interval.
Nat.nth is zero-indexed. Lower endpoint is strict; upper endpoint is closed. -/
def octic_block : Prop := ∀ u : ℝ, exp 24 ≤ u → ∀ m : ℕ,
  (m : ℝ) ≤ (9001 / 9000 + (29 / 5) / log u) * sqrt u →
  u < (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ∧
    (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ≤
      u + (43 / 20) * sqrt u * log u
/-- An actual cross-family cube consumer. This RH consequence is not claimed novel. -/
def successive_cubes : Prop := ∀ n : ℕ, exp 8 ≤ (n : ℝ) →
  ∃ p : ℕ, Nat.Prime p ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3
end PrimeQuantile.v1
