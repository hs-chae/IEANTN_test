/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ActualJIdentity
import Mathlib.NumberTheory.Harmonic.Bounds

namespace RHLimit.PrimePower
open Real Finset IEANTN
set_option maxHeartbeats 0

lemma primeCounting_le_self {x : ℝ} (hx : 0 ≤ x) : primeCounting x ≤ x := by
  have hcard : (Nat.primesLE ⌊x⌋₊).card ≤ ⌊x⌋₊ := by
    have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Icc 1 ⌊x⌋₊ := by
      intro p hp
      have hh := Nat.mem_primesLE.mp hp
      exact mem_Icc.mpr ⟨hh.2.one_le, hh.1⟩
    simpa using card_le_card hsub
  unfold primeCounting
  rw [Nat.primesLE_card_eq_primeCounting] at hcard
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hx)

lemma root_le_third {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 3 ≤ k) :
    x ^ (1 / (k : ℝ)) ≤ x ^ (1 / (3 : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)

lemma prime_counting_chebyshev {x : ℝ} (hx : 1 < x) :
    primeCounting x ≤ 2 * log 4 * x / log x + sqrt x := by
  have h := Chebyshev.pi_le_log4_mul_div hx
  change primeCounting x ≤ _ at h
  rw [Real.log_sqrt (by linarith : 0 ≤ x)] at h
  convert h using 1 <;> ring

lemma harmonic_tail {K : ℕ} (hK : 2 ≤ K) :
    (∑ j ∈ range (K-2), (1 : ℝ) / (j+3:ℝ)) ≤ log K := by
  have hh := harmonic_le_one_add_log K
  have he : (harmonic K : ℝ) = (3/2:ℝ) +
      ∑ j ∈ range (K-2), (1 : ℝ)/(j+3:ℝ) := by
    have hsum := sum_range_add (fun i : ℕ => ((i:ℝ)+1)⁻¹) 2 (K-2)
    have hKK : 2 + (K-2) = K := by omega
    rw [hKK] at hsum
    norm_num [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] at hsum
    simpa [harmonic, Rat.cast_sum, one_div, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm, add_left_comm] using hsum
  linarith

#print axioms primeCounting_le_self
#print axioms root_le_third
#print axioms prime_counting_chebyshev
#print axioms harmonic_tail
end RHLimit.PrimePower
