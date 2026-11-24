/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeInterval.v4
open Real Set IEANTN.PrimeWindows
/-- The complete original ordinary-pi target, with the exact original constants. -/
def count_215 : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (9001/9000 + (29/5)/log u) * sqrt u <
    primeCounting (u + (43/20)*sqrt u*log u) - primeCounting u
/-- The complete original count/width frontier. -/
def count_family : Prop := ∀ C ∈ Icc (103/100:ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
  ((8/9)*C - 911/1000 + (21/5)/log u) * sqrt u <
    primeCounting (u + C*sqrt u*log u) - primeCounting u
/-- Improved ordinary-pi lower count at unchanged width2.15. -/
def optimized_count_215 : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (180173/180000 + (29/5)/log u) * sqrt u <
    primeCounting (u + (43/20)*sqrt u*log u) - primeCounting u
/-- Both endpoints strictly excluded, with the stronger fixed count. -/
def optimized_strict_215 : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (180173/180000 + (29/5)/log u) * sqrt u <
    ((primesBetween u (u + (43/20)*sqrt u*log u)).card : ℝ)
/-- Stronger full real-C count frontier, with strict endpoints. -/
def optimized_strict_family : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ∀ u : ℝ, exp 24 ≤ u →
  ((8/9)*C - 18203/20000 + (21/5)/log u) * sqrt u <
    ((primesBetween u (u + C*sqrt u*log u)).card : ℝ)
/-- Width2.14891875 and leading count1, with strict endpoints. -/
def strict_214891875 : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (1 + (21/5)/log u) * sqrt u <
    ((primesBetween u (u + (343827/160000)*sqrt u*log u)).card : ℝ)
/-- Width2.149, retaining a uniform excess above leading count1. -/
def strict_2149_uniform : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (180013/180000 + (21/5)/log u) * sqrt u <
    ((primesBetween u (u + (2149/1000)*sqrt u*log u)).card : ℝ)
/-- Stronger full real-C ordinary-pi frontier. -/
def optimized_count_family : Prop := ∀ C ∈ Icc (103/100:ℝ) 16,
  ∀ u : ℝ, exp 24 ≤ u →
  ((8/9)*C - 18203/20000 + (21/5)/log u) * sqrt u <
    primeCounting (u + C*sqrt u*log u) - primeCounting u
end PrimeInterval.v4
