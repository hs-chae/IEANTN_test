/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card

namespace IEANTN

/-- Smaller prime entries of unordered Goldbach pairs, with an explicit cutoff.
The condition `2*p ≤ n` counts each unordered pair once; equality is allowed.
All uses here have `n ≥ 1000000`, so natural subtraction is in its source domain. -/
def goldbachPairStarts (n P : ℕ) : Finset ℕ :=
  (Finset.range (P+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p) ∧ 2*p ≤ n)

/-- Every even integer in the closed finite window has at least `K` distinct
unordered prime pairs whose smaller prime is at most `P`. -/
def GoldbachCountOn (A B P K : ℕ) : Prop :=
  ∀ n, A ≤ n → n ≤ B → n % 2 = 0 → K ≤ (goldbachPairStarts n P).card

end IEANTN
