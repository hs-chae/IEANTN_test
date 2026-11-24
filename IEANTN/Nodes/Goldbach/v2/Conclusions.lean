/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Goldbach
import IEANTN.Vocabulary.GoldbachCounts
import IEANTN.Vocabulary.PrimeWindows
namespace Goldbach.v2
open Real IEANTN
/-- Actual sorted triple counts from finite even Goldbach and the new strict
prime-window count. Not a new global odd-Goldbach existence record. -/
def octic_sorted_count : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  2*H<n → exp 24 ≤ (n:ℝ)-H →
  (343827/160000)*sqrt ((n:ℝ)-H)*log ((n:ℝ)-H) ≤ (H:ℝ)-4 →
  (1 + (21/5)/log ((n:ℝ)-H))*sqrt ((n:ℝ)-H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)
/-- Same-width2.15 sorted-triple gain, with the actual stronger leading count. -/
def octic_fixed_sorted_count : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  2*H<n → exp 24 ≤ (n:ℝ)-H →
  (43/20)*sqrt ((n:ℝ)-H)*log ((n:ℝ)-H) ≤ (H:ℝ)-4 →
  (180173/180000 + (29/5)/log ((n:ℝ)-H))*sqrt ((n:ℝ)-H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)
/-- Full sorted-triple count/width frontier, including every real C in the
original domain, finite Goldbach height and exact geometric applicability. -/
def octic_sorted_family : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  ∀ C ∈ Set.Icc (103/100:ℝ) 16, ∀ u : ℝ, exp 24 ≤ u → (n:ℝ)/2<u →
  u+C*sqrt u*log u ≤ (n:ℝ)-4 → (n:ℝ)-u ≤ (H:ℝ) →
  ((8/9)*C - 18203/20000 + (21/5)/log u)*sqrt u <
    ((GoldbachCounts.sortedTriples n).card : ℝ)
end Goldbach.v2
