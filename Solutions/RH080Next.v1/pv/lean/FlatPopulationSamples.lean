/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FlatPopulationBounds
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FlatPopulationPV.Model
open Real
noncomputable section

theorem term_error (j : Fin 16) (k : Nat) :
    |(weight j.val : ℝ)*(coefficient j.val : ℝ)*cos (2*π*j.val*((k : ℝ)/256))-
      signedTerm j.val k| ≤ 1000000000000 := by
  have hc := cosine_error j.val k
  have hs := signedSplit_error j.val k
  have hw : (weight j.val : ℝ) ≤ 2 := by exact_mod_cast weights_fit j.val
  have ha : (coefficient j.val : ℝ) ≤ 1000000000000000000 := by
    exact_mod_cast coefficients_fit j
  have hwa : (weight j.val : ℝ)*(coefficient j.val : ℝ) ≤ 2000000000000000000 := by
    nlinarith [mul_le_mul hw ha (Nat.cast_nonneg (coefficient j.val)) (by norm_num : (0:ℝ)≤2)]
  have h1 : |(weight j.val : ℝ)*(coefficient j.val : ℝ)*
      (cos (2*π*j.val*((k : ℝ)/256))-approxCos j.val k)| ≤
      (weight j.val : ℝ)*(coefficient j.val : ℝ)/10000000 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact (mul_le_mul_of_nonneg_left hc (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans_eq (by ring)
  have h2 : |(weight j.val : ℝ)*
      ((coefficient j.val : ℝ)*approxCos j.val k-signedSplit j.val k)| ≤
      (weight j.val : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (weight j.val))
  rw [signedTerm_eq]
  have ht := abs_add_le
    ((weight j.val : ℝ)*(coefficient j.val : ℝ)*
      (cos (2*π*j.val*((k : ℝ)/256))-approxCos j.val k))
    ((weight j.val : ℝ)*((coefficient j.val : ℝ)*approxCos j.val k-signedSplit j.val k))
  have he :
      (weight j.val : ℝ)*(coefficient j.val : ℝ)*(cos (2*π*j.val*((k : ℝ)/256))-approxCos j.val k)+
      (weight j.val : ℝ)*((coefficient j.val : ℝ)*approxCos j.val k-signedSplit j.val k) =
      (weight j.val : ℝ)*(coefficient j.val : ℝ)*cos (2*π*j.val*((k : ℝ)/256))-
      (weight j.val : ℝ)*signedSplit j.val k := by ring
  rw [he] at ht
  nlinarith

theorem sample_sum_error (k : Nat) :
    |(∑ j ∈ Finset.range 16, ((weight j*coefficient j : Nat) : ℝ)*
      cos (2*π*j*((k : ℝ)/256))) - ∑ j ∈ Finset.range 16, signedTerm j k| ≤
      16000000000000 := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range 16,
        |((weight j*coefficient j : Nat) : ℝ)*cos (2*π*j*((k : ℝ)/256))-signedTerm j k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range 16, (1000000000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_mul] using term_error ⟨j,Finset.mem_range.mp hj⟩ k
    _ = 16000000000000 := by norm_num

theorem sampleUpper_meaning (k : Nat) :
    |((rawSample k).1 : ℝ)-((rawSample k).2 : ℝ)|+100000000000000 =
      (sampleUpper k : ℝ) := by
  dsimp only [sampleUpper]
  split_ifs with h
  · have hc : ((rawSample k).2 : ℝ) ≤ ((rawSample k).1 : ℝ) := by exact_mod_cast h
    rw [Nat.cast_add, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hc)]
    norm_num
  · have hr : (rawSample k).1 ≤ (rawSample k).2 := by omega
    have hc : ((rawSample k).1 : ℝ) ≤ ((rawSample k).2 : ℝ) := by exact_mod_cast hr
    rw [Nat.cast_add, Nat.cast_sub hr, abs_of_nonpos (sub_nonpos.mpr hc)]
    norm_num

theorem actual_grid_enclosure (k : Nat) :
    |trigPolynomial ((k : ℝ)/256)| ≤ (sampleUpper k : ℝ)/1000000000000000000 := by
  have he := sample_sum_error k
  have ht := abs_add_le
    ((∑ j ∈ Finset.range 16, ((weight j*coefficient j : Nat) : ℝ)*
      cos (2*π*j*((k : ℝ)/256)))-∑ j ∈ Finset.range 16, signedTerm j k)
    (∑ j ∈ Finset.range 16, signedTerm j k)
  rw [sub_add_cancel] at ht
  have hs := sampleUpper_meaning k
  rw [rawSample_difference] at hs
  unfold trigPolynomial
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0:ℝ)<1000000000000000000)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

#print axioms term_error
#print axioms actual_grid_enclosure
end
end RH080Next.FlatPopulationPV.Model
