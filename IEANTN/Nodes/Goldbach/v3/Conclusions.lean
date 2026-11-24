/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Goldbach
import IEANTN.Vocabulary.GoldbachCounts
import IEANTN.Vocabulary.PrimeWindows

namespace Goldbach.v3
open Real IEANTN

/-- Internal range/multiplicity transfer: selected primes above n/3 can occur
as at most two components of a sorted triple. The finite binary hypothesis is
explicit; the new range is3H≤2n rather than the old2H<n. -/
def sorted_count_extended : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  3 * H ≤ 2 * n → exp 24 ≤ (n : ℝ) - H →
  (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4 →
  (1 / 2 + (21 / 10) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)

/-- With no n/H ratio assumption, a sorted triple has at most three selected
components. The actual onset and finite width budget remain explicit. -/
def sorted_count_full_finite_range : Prop := ∀ H n : ℕ, GoldbachEvenUpTo H → Odd n →
  exp 24 ≤ (n : ℝ) - H →
  (343827 / 160000) * sqrt ((n : ℝ) - H) * log ((n : ℝ) - H) ≤ (H : ℝ) - 4 →
  (1 / 3 + (7 / 5) / log ((n : ℝ) - H)) * sqrt ((n : ℝ) - H) <
    ((GoldbachCounts.sortedTriples n).card : ℝ)

/-- Every odd n in the explicit newly covered band[6e18,8e18] has more than
750million actual sorted triples, conditional on the finite binary input4e18.
All scalar geometry is discharged by the solution. The old n>8e18 injection
covered none of this band. This is not a new global Goldbach existence record. -/
def sorted_count_750m_band : Prop := GoldbachEvenUpTo 4000000000000000000 →
  ∀ n : ℕ, Odd n → 6000000000000000000 ≤ n → n ≤ 8000000000000000000 →
    (750000000 : ℝ) < ((GoldbachCounts.sortedTriples n).card : ℝ)

end Goldbach.v3
