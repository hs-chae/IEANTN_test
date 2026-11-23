/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PrimePowerRemainder

namespace RHLimit.PrimePower
open Real IEANTN
set_option maxHeartbeats 0

noncomputable def elementaryRemainder (L : ℝ) : ℝ :=
  2 * log 4 * exp (L/2) / L + exp (L/4) / 2 +
    exp (L/3) * log (L / log 2)

lemma sqrt_exp_eq (L : ℝ) : sqrt (exp L) = exp (L/2) := by
  rw [sqrt_eq_rpow, ← exp_mul]
  congr 1
  ring

lemma exp_two_ge_four : (4:ℝ) ≤ exp 2 := by
  calc (4:ℝ) = 2^2 := by norm_num
    _ ≤ (exp 1)^2 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le 2
    _ = exp 2 := by rw [← Real.exp_nat_mul]; congr 1; norm_num

lemma square_prime_bound {L : ℝ} (hL : 0 < L) :
    primeCounting (sqrt (exp L)) / 2 ≤
      2 * log 4 * exp (L/2) / L + exp (L/4)/2 := by
  rw [sqrt_exp_eq]
  have hp := prime_counting_chebyshev (one_lt_exp_iff.mpr (by linarith : 0 < L/2))
  rw [log_exp, sqrt_exp_eq] at hp
  have he : (L/2)/2 = L/4 := by ring
  rw [he] at hp
  have hh := div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ)≤2)
  calc
    primeCounting (exp (L/2))/2 ≤
        (2 * log 4 * exp (L/2)/(L/2) + exp (L/4))/2 := hh
    _ = 2 * log 4 * exp (L/2)/L + exp (L/4)/2 := by
      field_simp [hL.ne']
      <;> ring

lemma height_log_bound {L : ℝ} (hL : 2 ≤ L) :
    log (heightCount (exp L)) ≤ log (L / log 2) := by
  have hx : (4:ℝ) ≤ exp L := exp_two_ge_four.trans (exp_le_exp.mpr hL)
  have hK := heightCount_ge_two hx
  have hK0 : (0:ℝ) < heightCount (exp L) := by exact_mod_cast (by omega : 0 < heightCount (exp L))
  apply log_le_log hK0
  unfold heightCount
  rw [log_exp]
  exact Nat.floor_le (div_nonneg (by linarith) (log_pos (by norm_num)).le)

/-- A wholly elementary upper bound for the actual lower-height prime-power
correction. No RH, zeta estimate, prime table or numerical premise is used. -/
theorem actual_remainder_elementary {L : ℝ} (hL : 2 ≤ L) :
    riemannPrimeCounting (exp L) - primeCounting (exp L) ≤ elementaryRemainder L := by
  have hx : (4:ℝ) ≤ exp L := exp_two_ge_four.trans (exp_le_exp.mpr hL)
  have h := remainder_upper_with_square hx
  have hpow : (exp L) ^ (1/(3:ℝ)) = exp (L/3) := by
    rw [← exp_mul]
    congr 1
    ring
  rw [hpow] at h
  have hs := square_prime_bound (by linarith : 0 < L)
  have ht := mul_le_mul_of_nonneg_left (height_log_bound hL) (exp_pos (L/3)).le
  unfold elementaryRemainder
  linarith

#print axioms square_prime_bound
#print axioms height_log_bound
#print axioms actual_remainder_elementary
end RHLimit.PrimePower
