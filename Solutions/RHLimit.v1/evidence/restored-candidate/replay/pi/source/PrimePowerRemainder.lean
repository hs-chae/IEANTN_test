/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PrimePowerBounds

namespace RHLimit.PrimePower
open Real Finset IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

noncomputable def heightCount (x : ℝ) : ℕ := ⌊log x / log 2⌋₊

lemma remainder_finite {x : ℝ} (hx : 0 < x) :
    riemannPrimeCounting x - primeCounting x =
      ∑ j ∈ range (heightCount x - 1),
        primeCounting (x ^ (1 / (j+2:ℝ))) / (j+2:ℝ) := by
  rw [actual_prime_power_series hx]
  apply tsum_eq_sum
  intro j hj
  have h : heightCount x ≤ j+1 := by
    have hh : heightCount x - 1 ≤ j := by simpa only [mem_range, not_lt] using hj
    omega
  have hz := prime_root_zero_past_log hx (k:=j+1) h
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hz
  simp only [one_div, hz, zero_div]

lemma heightCount_ge_two {x : ℝ} (hx : 4 ≤ x) : 2 ≤ heightCount x := by
  apply Nat.le_floor
  norm_num only [Nat.cast_ofNat]
  have hlog := log_le_log (by norm_num : (0:ℝ)<4) hx
  have he : log (4:ℝ) = 2 * log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  exact (le_div_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr (by linarith)

lemma remainder_square_tail {x : ℝ} (hx : 4 ≤ x) :
    riemannPrimeCounting x - primeCounting x =
      primeCounting (sqrt x) / 2 +
      ∑ j ∈ range (heightCount x - 2),
        primeCounting (x ^ (1 / (j+3:ℝ))) / (j+3:ℝ) := by
  rw [remainder_finite (by linarith : 0 < x)]
  have hK := heightCount_ge_two hx
  rw [show heightCount x - 1 = (heightCount x-2)+1 by omega, sum_range_succ']
  simp only [Nat.cast_zero, zero_add]
  rw [← Real.sqrt_eq_rpow, add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

lemma remainder_upper_with_square {x : ℝ} (hx : 4 ≤ x) :
    riemannPrimeCounting x - primeCounting x ≤
      primeCounting (sqrt x) / 2 + x ^ (1 / (3:ℝ)) * log (heightCount x) := by
  rw [remainder_square_tail hx]
  refine add_le_add le_rfl ?_
  calc
    (∑ j ∈ range (heightCount x-2),
        primeCounting (x ^ (1/(j+3:ℝ)))/(j+3:ℝ))
      ≤ ∑ j ∈ range (heightCount x-2), x ^ (1/(3:ℝ))/(j+3:ℝ) := by
          apply sum_le_sum
          intro j hj
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact (primeCounting_le_self (Real.rpow_nonneg (by linarith : 0 ≤ x) _)).trans
            (by simpa only [Nat.cast_add, Nat.cast_ofNat] using
              (root_le_third (k:=j+3) (by linarith : 1 ≤ x) (by omega : 3 ≤ j+3)))
    _ = x ^ (1/(3:ℝ)) * ∑ j ∈ range (heightCount x-2), (1:ℝ)/(j+3:ℝ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j hj
          ring
    _ ≤ x ^ (1/(3:ℝ)) * log (heightCount x) :=
          mul_le_mul_of_nonneg_left (harmonic_tail (heightCount_ge_two hx))
            (Real.rpow_nonneg (by linarith) _)

#print axioms remainder_finite
#print axioms remainder_square_tail
#print axioms remainder_upper_with_square
end RHLimit.PrimePower
