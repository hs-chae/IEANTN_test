/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalFrontierTransport
import IEANTN.Nodes.Goldbach.v3.Conclusions

namespace Goldbach.v3

theorem challenge_sorted_count_extended
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_extended := by
  intro H n hEven hn hnH hu hwidth
  exact RHOnePrime.Canonical.extended_from_family hi hEven hn hnH hu hwidth

theorem challenge_sorted_count_full_finite_range
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_full_finite_range := by
  intro H n hEven hn hu hwidth
  exact RHOnePrime.Canonical.full_range_from_family hi hEven hn hu hwidth

theorem challenge_sorted_count_750m_band
    (hi : PrimeInterval.v4.optimized_strict_family) : sorted_count_750m_band := by
  intro hEven n hn hnlow hnupper
  exact RHOnePrime.Canonical.numeric_band_from_family hi hEven hn hnlow hnupper

#print axioms challenge_sorted_count_extended
#print axioms challenge_sorted_count_full_finite_range
#print axioms challenge_sorted_count_750m_band
end Goldbach.v3
