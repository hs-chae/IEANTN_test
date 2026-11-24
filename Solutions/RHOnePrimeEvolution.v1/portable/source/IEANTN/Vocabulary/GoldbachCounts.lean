/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
namespace IEANTN.GoldbachCounts
/-- Sorted prime triples, allowing repeated primes. Each coordinate is bounded
by n; the exact finite construction is shared with the application proof. -/
noncomputable def sortedTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)).product
    ((Finset.range (n + 1)).product (Finset.range (n + 1)))).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n)
end IEANTN.GoldbachCounts
