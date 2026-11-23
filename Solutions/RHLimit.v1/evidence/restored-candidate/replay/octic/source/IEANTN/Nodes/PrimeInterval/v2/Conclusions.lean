/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeWindows
namespace PrimeInterval.v2
open Real Set IEANTN.PrimeWindows
/-- Strict actual prime-count lower bound on the complete real ray. -/
def count_215 : Prop := ∀ u : ℝ, exp 24 ≤ u →
  (9001 / 9000 + (29 / 5) / log u) * sqrt u <
    primeCounting (u + (43 / 20) * sqrt u * log u) - primeCounting u
/-- Full reusable count/width frontier, not just prime existence. -/
def count_family : Prop := ∀ C ∈ Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
  ((8 / 9) * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
    primeCounting (u + C * sqrt u * log u) - primeCounting u
end PrimeInterval.v2
