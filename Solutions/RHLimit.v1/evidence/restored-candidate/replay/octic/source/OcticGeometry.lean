/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
import EvenKernel

namespace RHLimit.OcticGeometry
open Real Set
set_option maxHeartbeats 2000000

theorem exp_twelve_lower : (160000 : ℝ) < exp 12 := by
  have he : (1359 / 500 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 1359 / 500)
    (by norm_num : (12 : ℕ) ≠ 0)
  have hn : (160000 : ℝ) < (1359 / 500 : ℝ) ^ 12 := by norm_num
  rw [← Real.exp_nat_mul] at hp
  have hp' : (1359 / 500 : ℝ) ^ 12 < exp 12 := by
    simpa only [Nat.cast_ofNat, mul_one] using hp
  exact hn.trans hp'

theorem exp_seventeen_quarters_upper : exp (17 / 4 : ℝ) < 71 := by
  have he : exp 1 < (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_lt_pow_left₀ he (Real.exp_nonneg 1) (by norm_num : (17 : ℕ) ≠ 0)
  have hn : (68 / 25 : ℝ) ^ 17 < (71 : ℝ) ^ 4 := by norm_num
  have hrel : exp (17 / 4 : ℝ) ^ 4 = exp 1 ^ 17 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlt : exp (17 / 4 : ℝ) ^ 4 < (71 : ℝ) ^ 4 := by rw [hrel]; exact hp.trans hn
  by_contra h
  have hge : (71 : ℝ) ≤ exp (17 / 4 : ℝ) := le_of_not_gt h
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 71) hge 4
  linarith

theorem exp_half_lower {L : ℝ} (hL : 24 ≤ L) :
    (2500 / 9 : ℝ) * L ^ 2 ≤ exp (L / 2) := by
  have ht0 : 0 ≤ L / 2 - 12 := by linarith
  have he := Real.sum_le_exp_of_nonneg ht0 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have ht : (L / 24) ^ 2 ≤ exp (L / 2 - 12) := by
    nlinarith [sq_nonneg (L / 2 - 12)]
  have hc := mul_le_mul_of_nonneg_right exp_twelve_lower.le (sq_nonneg (L / 24))
  have hb : (2500 / 9 : ℝ) * L ^ 2 ≤ exp 12 * (L / 24) ^ 2 := by nlinarith
  calc
    (2500 / 9 : ℝ) * L ^ 2 ≤ exp 12 * (L / 24) ^ 2 := hb
    _ ≤ exp 12 * exp (L / 2 - 12) := mul_le_mul_of_nonneg_left ht (exp_nonneg 12)
    _ = exp (L / 2) := by rw [← Real.exp_add]; congr 1; ring

theorem D_nonneg {C L : ℝ} (hC : (103 / 100 : ℝ) ≤ C) (hL : 24 ≤ L) :
    0 ≤ EvenKernel.D C L := by
  have hm := mul_le_mul hC hL (by norm_num : (0 : ℝ) ≤ 24)
    (by linarith : 0 ≤ C)
  unfold EvenKernel.D
  nlinarith

theorem D_le_half {C L : ℝ} (hL : 0 ≤ L) :
    EvenKernel.D C L ≤ C / 2 * L := by
  unfold EvenKernel.D
  linarith

theorem delta_eq_div (C L : ℝ) :
    EvenKernel.δ C L = EvenKernel.D C L / exp (L / 2) := by
  unfold EvenKernel.δ
  rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
  rfl

theorem delta_nonneg {C L : ℝ} (hC : (103 / 100 : ℝ) ≤ C) (hL : 24 ≤ L) :
    0 ≤ EvenKernel.δ C L := by
  unfold EvenKernel.δ
  exact mul_nonneg (D_nonneg hC hL) (exp_nonneg _)

theorem delta_scaled {C L : ℝ} (hC : (103 / 100 : ℝ) ≤ C) (hL : 24 ≤ L) :
    EvenKernel.δ C L ≤ (9 * C) / (5000 * L) := by
  have hLp : 0 < L := by linarith
  have hCp : 0 < C := by linarith
  have he := exp_half_lower hL
  rw [delta_eq_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 5000 * L)).mpr
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 9 * C)
  have hd := D_le_half (C := C) hLp.le
  have hd' := mul_le_mul_of_nonneg_right hd (show 0 ≤ 5000 * L by positivity)
  nlinarith

theorem delta_small {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : EvenKernel.δ C L ≤ 3 / 2500 := by
  have hs := delta_scaled hC.1 hL
  have hLp : 0 < L := by linarith
  have hb : (9 * C) / (5000 * L) ≤ (3 / 2500 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5000 * L)).mpr
    nlinarith [hC.2]
  exact hs.trans hb

theorem width_budget {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : 4 * C * L * EvenKernel.δ C L ≤ 1152 / 625 := by
  have hs := delta_scaled hC.1 hL
  have hCp : 0 < C := by linarith [hC.1]
  have hLp : 0 < L := by linarith
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * C * L by positivity)
  have heq : 4 * C * L * ((9 * C) / (5000 * L)) = (9 / 1250 : ℝ) * C ^ 2 := by
    field_simp
    <;> ring
  rw [heq] at hm
  have hsq : C ^ 2 ≤ (256 : ℝ) := by nlinarith [hC.2]
  nlinarith

theorem D_family_lower {C L : ℝ} (hC : (103 / 100 : ℝ) ≤ C) (hL : 24 ≤ L) :
    (284 / 25 : ℝ) ≤ EvenKernel.D C L := by
  have hm := mul_le_mul hC hL (by norm_num : (0 : ℝ) ≤ 24)
    (by linarith : 0 ≤ C)
  unfold EvenKernel.D
  nlinarith

theorem scalar_geometry_core {C η R P T : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hη : 0 < η) (hlam : 0 ≤ EvenKernel.countCoefficient 4 (911 / 500) C)
    (hm : ∀ L : ℝ, 24 ≤ L → η < (911 / 500 : ℝ) * log (2 * π * EvenKernel.D C L)
      - EvenKernel.mass 4 - 3 / 2 - R - P - T) :
    EvenKernel.ScalarGeometry 4 C (911 / 500) (3 / 2) R P T η := by
  intro L hL
  have hd := delta_nonneg hC.1 hL
  have hs := delta_small hC hL
  refine ⟨exp_pos _, ?_, ?_, ?_, hd, D_nonneg hC.1 hL, hlam, hη, hm L hL⟩
  · unfold EvenKernel.a
    rw [Real.log_exp]
    linarith
  · unfold EvenKernel.a EvenKernel.b
    apply Real.exp_le_exp.mpr
    linarith
  · unfold EvenKernel.a
    rw [Real.log_exp]

theorem scalar_geometry_family {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.ScalarGeometry 4 C (911 / 500) (3 / 2)
      (3 / 20) (29 / 500) (1 / 1000) (21 / 5) := by
  apply scalar_geometry_core hC (by norm_num)
  · norm_num [EvenKernel.countCoefficient, EvenKernel.mass]
    linarith [hC.1]
  intro L hL
  have hd := D_family_lower hC.1 hL
  have hπ : (157 / 50 : ℝ) ≤ π := by linarith [Real.pi_gt_d2]
  have hm := mul_le_mul hπ hd (by norm_num : (0 : ℝ) ≤ 284 / 25) pi_pos.le
  have harg : (71 : ℝ) ≤ 2 * π * EvenKernel.D C L := by nlinarith
  have hlog : (17 / 4 : ℝ) ≤ log (2 * π * EvenKernel.D C L) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 2 * π * EvenKernel.D C L)).mpr
    exact exp_seventeen_quarters_upper.le.trans harg
  norm_num [EvenKernel.mass]
  linarith

theorem exp_161_32_upper : exp (161 / 32 : ℝ) < 154 := by
  have he : exp 1 < (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_lt_pow_left₀ he (Real.exp_nonneg 1) (by norm_num : (161 : ℕ) ≠ 0)
  have hn : (68 / 25 : ℝ) ^ 161 < (154 : ℝ) ^ 32 := by norm_num
  have hrel : exp (161 / 32 : ℝ) ^ 32 = exp 1 ^ 161 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlt : exp (161 / 32 : ℝ) ^ 32 < (154 : ℝ) ^ 32 := by
    rw [hrel]
    exact hp.trans hn
  by_contra h
  have hge : (154 : ℝ) ≤ exp (161 / 32 : ℝ) := le_of_not_gt h
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 154) hge 32
  linarith

theorem scalar_geometry_215 :
    EvenKernel.ScalarGeometry 4 (43 / 20) (911 / 500) (3 / 2)
      (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) := by
  apply scalar_geometry_core (by norm_num : (43 / 20 : ℝ) ∈ Icc (103 / 100 : ℝ) 16)
    (by norm_num)
  · norm_num [EvenKernel.countCoefficient, EvenKernel.mass]
  intro L hL
  have hd : (124 / 5 : ℝ) ≤ EvenKernel.D (43 / 20) L := by
    unfold EvenKernel.D
    linarith
  have hπ : (157 / 50 : ℝ) ≤ π := by linarith [Real.pi_gt_d2]
  have hm := mul_le_mul hπ hd (by norm_num : (0 : ℝ) ≤ 124 / 5) pi_pos.le
  have harg : (154 : ℝ) ≤ 2 * π * EvenKernel.D (43 / 20) L := by nlinarith
  have hlog : (161 / 32 : ℝ) ≤ log (2 * π * EvenKernel.D (43 / 20) L) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 2 * π * EvenKernel.D (43 / 20) L)).mpr
    exact exp_161_32_upper.le.trans harg
  norm_num [EvenKernel.mass]
  linarith

#print axioms exp_half_lower
#print axioms delta_scaled
#print axioms width_budget
#print axioms scalar_geometry_family
#print axioms scalar_geometry_215
end RHLimit.OcticGeometry
