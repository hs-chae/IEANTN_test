/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

/-! Pure scalar verification of a conservative RETUNED published margin.
Constants come from BlanquerRobles2026v2,Table3/Eq20–21(pp13–14).
This file does NOT prove a variable-c version of the paper's fixed-c analytic
reduction, establish its FFT norm in Lean, or prove a new prime theorem.
-/
noncomputable section
namespace RHOnePrime.Published2026Scalar
open Real Set
set_option maxHeartbeats 0

def margin811 (t : ℝ) : ℝ :=
  (((811 / 1000) * (92045248904315389 / 100000000000000000) -
    78353189999070 / 100000000000000) / 2) * t +
  (78353189999069 / 100000000000000) *
    log ((811 / 1000) * t * log 2 / 2) - 1101508373007 / 1000000000000

lemma endpoint44 : (7 / 10000 : ℝ) < margin811 44 := by
  have hm := log_le_log (by norm_num : (0 : ℝ) < 8 * (77 / 50))
    (show (8 : ℝ) * (77 / 50) ≤ (811 / 1000) * 44 * log 2 / 2 by
      nlinarith [Real.log_two_gt_d9])
  rw [log_mul (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (77 / 50 : ℝ) ≠ 0)] at hm
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, log_pow]
    norm_num
  rw [h8] at hm
  have hs := le_log_one_add_of_nonneg (x := (27 / 50 : ℝ)) (by norm_num)
  norm_num at hs
  have hl : 3 * log 2 + (54 / 127 : ℝ) ≤ log ((811 / 1000) * 44 * log 2 / 2) := by
    linarith
  unfold margin811
  nlinarith [Real.log_two_gt_d9]

lemma endpoint60 : (7 / 10000 : ℝ) < margin811 60 := by
  have hm := log_le_log (by norm_num : (0 : ℝ) < 16 * (527 / 500))
    (show (16 : ℝ) * (527 / 500) ≤ (811 / 1000) * 60 * log 2 / 2 by
      nlinarith [Real.log_two_gt_d9])
  rw [log_mul (by norm_num : (16 : ℝ) ≠ 0) (by norm_num : (527 / 500 : ℝ) ≠ 0)] at hm
  have h16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, log_pow]
    norm_num
  rw [h16] at hm
  have hs := le_log_one_add_of_nonneg (x := (27 / 500 : ℝ)) (by norm_num)
  norm_num at hs
  have hl : 4 * log 2 + (54 / 1027 : ℝ) ≤ log ((811 / 1000) * 60 * log 2 / 2) := by
    linarith
  unfold margin811
  nlinarith [Real.log_two_gt_d9]

/-- The entire real continuum is proved by log concavity and two kernel
endpoint certificates, not by a finite grid or an unverified Arb observation. -/
theorem whole_slab_lower {t : ℝ} (ht : t ∈ Icc (44 : ℝ) 60) :
    (7 / 10000 : ℝ) ≤ margin811 t := by
  let a : ℝ := (60 - t) / 16
  let b : ℝ := (t - 44) / 16
  have ha : 0 ≤ a := by dsimp [a]; linarith [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have harg44 : 0 < (811 / 1000 : ℝ) * 44 * log 2 / 2 := by positivity
  have harg60 : 0 < (811 / 1000 : ℝ) * 60 * log 2 / 2 := by positivity
  have hl := strictConcaveOn_log_Ioi.concaveOn.2 harg44 harg60 ha hb hab
  simp only [smul_eq_mul] at hl
  have he : a * ((811 / 1000 : ℝ) * 44 * log 2 / 2) +
      b * ((811 / 1000 : ℝ) * 60 * log 2 / 2) = (811 / 1000) * t * log 2 / 2 := by
    dsimp [a, b]
    ring
  rw [he] at hl
  have hweighted : a * margin811 44 + b * margin811 60 ≤ margin811 t := by
    have hp := mul_le_mul_of_nonneg_left hl
      (by norm_num : (0 : ℝ) ≤ 78353189999069 / 100000000000000)
    dsimp [margin811, a, b] at hp ⊢
    nlinarith
  have h44 := mul_le_mul_of_nonneg_left endpoint44.le ha
  have h60 := mul_le_mul_of_nonneg_left endpoint60.le hb
  nlinarith

theorem whole_slab_positive {t : ℝ} (ht : t ∈ Icc (44 : ℝ) 60) :
    0 < margin811 t := lt_of_lt_of_le (by norm_num) (whole_slab_lower ht)

#print axioms endpoint44
#print axioms endpoint60
#print axioms whole_slab_lower
#print axioms whole_slab_positive
end RHOnePrime.Published2026Scalar
