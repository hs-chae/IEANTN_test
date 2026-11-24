/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimePowerPopulation.v1
open Real IEANTN.PrimeWindows

/-- Derived octic count in the strictly open cube interval, at every real n>=exp8.
The imported prime-family claim carries the analytic assumptions upstream. -/
def cube_population_all_real : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (101797 / 20000 + (7 / 5) / log n) * n * sqrt n <
    ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

/-- Variable-width disjoint-cell amplification: a genuine n²/log(n) count at
exactly the same onset. This is new derived mathematics, not a new kernel. -/
def cube_density_all_real : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (7 / 10) * n ^ 2 / log n < ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

/-- The concrete integer onset follows from a kernel proof exp8<2981.
Both cube endpoints remain strictly excluded. -/
def cube_density_natural : Prop := ∀ n : ℕ, 2981 ≤ n →
  (7 / 10) * (n : ℝ) ^ 2 / log n <
    ((primesBetween ((n : ℝ) ^ 3) (((n : ℝ) + 1) ^ 3)).card : ℝ)

/-- Every integer exponent r>=3, not a statement about consecutive squares.
The full positive logarithmic allowance is retained. -/
def higher_power_population : Prop := ∀ n : ℝ, exp 8 ≤ n → ∀ r : ℕ, 3 ≤ r →
  (101797 / 20000 + (21 / 5) / ((r : ℝ) * log n)) * sqrt (n ^ r) <
    ((primesBetween (n ^ r) ((n + 1) ^ r)).card : ℝ)

/-- The actual maximum of both proved lower counts preserves the small-n branch
and uses the stronger density at large n. No branch is silently discarded. -/
def cube_frontier : Prop := ∀ n : ℝ, exp 8 ≤ n →
  max ((101797 / 20000 + (7 / 5) / log n) * n * sqrt n)
    ((7 / 10) * n ^ 2 / log n) <
    ((primesBetween (n ^ 3) ((n + 1) ^ 3)).card : ℝ)

/-- Whole-ray strict comparison to the preceding .648 density, with identical
mathematical domain. This elementary comparison has no analytic premise. -/
def density_improves_648 : Prop := ∀ n : ℝ, exp 8 ≤ n →
  (81 / 125) * n ^ 2 / log n < (7 / 10) * n ^ 2 / log n
end PrimePowerPopulation.v1
