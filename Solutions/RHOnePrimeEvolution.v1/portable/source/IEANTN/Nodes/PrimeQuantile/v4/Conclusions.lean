/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows

namespace PrimeQuantile.v4
open Real

/-- Actual contiguous prime block with both endpoints strict. The index is
zero-based: primeCounting(floor x)+m selects the(m+1)st prime strictly above x.
The entire generic octic lower margin is retained for every supported width. -/
def strict_generic_block : Prop := ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
  ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
    (m : ℝ) ≤ (8 / 9 * C - 18203 / 20000 + (21 / 5) / log x) * sqrt x →
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + C * sqrt x * log x

/-- Preserve the specialized2.15 count, including its stronger5.8/log term;
only the old closed upper endpoint is strengthened to strict. -/
def strict_special_block : Prop := ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
  (m : ℝ) ≤ (180173 / 180000 + (29 / 5) / log x) * sqrt x →
  x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
    (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
      x + (43 / 20) * sqrt x * log x

/-- Recovering the positive logarithmic population term shortens the interval
by exactly4.725sqrt(x) while retaining every index target m≤sqrt(x).
The original larger count in the fixed window remains a separate conclusion. -/
def shifted_sqrt_block : Prop := ∀ x : ℝ, exp 24 ≤ x → ∀ m : ℕ,
  (m : ℝ) ≤ sqrt x →
  x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
    (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
      x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x

end PrimeQuantile.v4
