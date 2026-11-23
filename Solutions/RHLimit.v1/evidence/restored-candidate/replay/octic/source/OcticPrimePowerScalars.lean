/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticPrimePowers

namespace RHLimit.OcticPrimePowers
open Real Set
open RHLimit.OcticGeometry
set_option maxHeartbeats 2000000

theorem exp_twelve_sharp : (162500 : ℝ) < exp 12 := by
  have he : (1359 / 500 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 1359 / 500)
    (by norm_num : (12 : ℕ) ≠ 0)
  have hn : (162500 : ℝ) < (1359 / 500 : ℝ) ^ 12 := by norm_num
  rw [← Real.exp_nat_mul] at hp
  have hp' : (1359 / 500 : ℝ) ^ 12 < exp 12 := by
    simpa only [Nat.cast_ofNat, mul_one] using hp
  exact hn.trans hp'

theorem exp_half_sharp {L : ℝ} (hL : 24 ≤ L) :
    (40625 / 144 : ℝ) * L ^ 2 ≤ exp (L / 2) := by
  have ht0 : 0 ≤ L / 2 - 12 := by linarith
  have he := Real.sum_le_exp_of_nonneg ht0 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have ht : (L / 24) ^ 2 ≤ exp (L / 2 - 12) := by
    nlinarith [sq_nonneg (L / 2 - 12)]
  have hc := mul_le_mul_of_nonneg_right exp_twelve_sharp.le (sq_nonneg (L / 24))
  have hb : (40625 / 144 : ℝ) * L ^ 2 ≤ exp 12 * (L / 24) ^ 2 := by nlinarith
  calc
    _ ≤ exp 12 * (L / 24) ^ 2 := hb
    _ ≤ exp 12 * exp (L / 2 - 12) := mul_le_mul_of_nonneg_left ht (exp_nonneg 12)
    _ = exp (L / 2) := by rw [← Real.exp_add]; congr 1; ring

theorem exp_delta_half_upper {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : exp (EvenKernel.δ C L / 2) ≤ 1001 / 1000 := by
  have hd := delta_nonneg hC.1 hL
  have hu := delta_small hC hL
  have he := Real.abs_exp_sub_one_sub_id_le
    (show |EvenKernel.δ C L / 2| ≤ 1 by rw [abs_of_nonneg (by positivity)]; linarith)
  have hh := (abs_le.mp he).2
  have hsq : (EvenKernel.δ C L / 2) ^ 2 ≤ (3 / 5000 : ℝ) ^ 2 := by nlinarith
  norm_num at hsq
  linarith

theorem log_b_upper {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : log (EvenKernel.b C L) ≤ (1001 / 1000 : ℝ) * L := by
  have hu := delta_small hC hL
  unfold EvenKernel.b
  rw [Real.log_exp]
  linarith

theorem exponent_cutoff_bounds {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) :
    1 ≤ ⌊log (EvenKernel.b C L) / log 2⌋₊ ∧
      (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ) ≤ 3 * L := by
  have hd := delta_nonneg hC.1 hL
  have hu := delta_small hC hL
  have hlb : log (EvenKernel.b C L) = L + EvenKernel.δ C L := Real.log_exp _
  have hl2p : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl2u : log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2l : (1 / 2 : ℝ) ≤ log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  constructor
  · apply (Nat.one_le_floor_iff _).mpr
    apply (one_le_div hl2p).mpr
    rw [hlb]
    linarith
  · have hn : 0 ≤ log (EvenKernel.b C L) / log 2 := by rw [hlb]; positivity
    have hf := Nat.floor_le hn
    apply hf.trans
    apply (div_le_iff₀ hl2p).mpr
    rw [hlb]
    have hm := mul_le_mul_of_nonneg_left hl2l (by linarith : 0 ≤ 3 * L)
    linarith

theorem log_three_mul_le_quarter {L : ℝ} (hL : 24 ≤ L) :
    log (3 * L) ≤ L / 4 := by
  have he : (27 / 10 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 27 / 10)
    (by norm_num : (5 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  have hp' : (72 : ℝ) ≤ exp 5 := by
    norm_num at hp
    linarith
  have h72 : log (72 : ℝ) ≤ 5 := (Real.log_le_iff_le_exp (by norm_num)).mpr hp'
  have hLp : 0 < L := by linarith
  have hx : 0 < L / 24 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  have heq : log (3 * L) = log 72 + log (L / 24) := by
    rw [← Real.log_mul (by norm_num : (72 : ℝ) ≠ 0) hx.ne']
    congr 1
    ring
  rw [heq]
  linarith

theorem log_cutoff_le_quarter {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) : log (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ) ≤ L / 4 := by
  have hh := exponent_cutoff_bounds hC hL
  have hk : (0 : ℝ) < ⌊log (EvenKernel.b C L) / log 2⌋₊ := by
    exact_mod_cast (by omega : 0 < ⌊log (EvenKernel.b C L) / log 2⌋₊)
  exact (Real.log_le_log hk hh.2).trans (log_three_mul_le_quarter hL)

theorem prefactor_bound {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) :
    log (EvenKernel.b C L) / sqrt (EvenKernel.a C L) ≤
      (1001 / 1000 : ℝ) ^ 2 * L / exp (L / 2) := by
  have hd := delta_nonneg hC.1 hL
  have hlogb : 0 ≤ log (EvenKernel.b C L) := by
    unfold EvenKernel.b
    rw [Real.log_exp]
    linarith
  have heq : sqrt (EvenKernel.a C L) = exp (L / 2) / exp (EvenKernel.δ C L / 2) := by
    unfold EvenKernel.a
    rw [← Real.exp_half, ← Real.exp_sub]
    congr 1
    ring
  rw [heq]
  have hmul := mul_le_mul (log_b_upper hC hL) (exp_delta_half_upper hC hL)
    (exp_nonneg _) (show 0 ≤ (1001 / 1000 : ℝ) * L by linarith)
  calc
    _ = log (EvenKernel.b C L) * exp (EvenKernel.δ C L / 2) / exp (L / 2) := by
      field_simp
    _ ≤ ((1001 / 1000 : ℝ) * L * (1001 / 1000)) / exp (L / 2) :=
      div_le_div_of_nonneg_right hmul (exp_nonneg _)
    _ = _ := by ring

theorem delta_sqrt_b_bound {C L : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) :
    2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) ≤
      C * L * (1001 / 1000 : ℝ) := by
  have hCp : 0 < C := by linarith [hC.1]
  have hLp : 0 < L := by linarith
  have heq : 2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) =
      (C * L - 2) * exp (EvenKernel.δ C L / 2) := by
    unfold EvenKernel.b
    rw [← Real.exp_half]
    have hh : (L + EvenKernel.δ C L) / 2 = L / 2 + EvenKernel.δ C L / 2 := by ring
    rw [hh, Real.exp_add, delta_eq_div]
    unfold EvenKernel.D
    field_simp
    <;> ring
  rw [heq]
  have hm := mul_le_mul_of_nonneg_left (exp_delta_half_upper hC hL)
    (show 0 ≤ C * L - 2 by nlinarith [hC.1])
  nlinarith

theorem primepower_cost_scalar (n : ℕ) {C L : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    EvenKernel.mangoldtPopulation n C L - EvenKernel.population n C L ≤
      (1001 / 1000 : ℝ) ^ 2 * (C * (1001 / 1000) + 1 / 4) * (144 / 40625) := by
  have hd := delta_nonneg hC.1 hL
  have hLp : 0 < L := by linarith
  have hlb : 0 ≤ log (EvenKernel.b C L) := by
    unfold EvenKernel.b
    rw [Real.log_exp]
    linarith
  have hp0 : 0 ≤ log (EvenKernel.b C L) / sqrt (EvenKernel.a C L) := by positivity
  have hinner : 2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) +
      log (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ) ≤
      (C * (1001 / 1000 : ℝ) + 1 / 4) * L := by
    have h1 := delta_sqrt_b_bound hC hL
    have h2 := log_cutoff_le_quarter hC hL
    nlinarith
  have hinner0 : 0 ≤ (C * (1001 / 1000 : ℝ) + 1 / 4) * L := by
    have hCp : 0 ≤ C := by linarith [hC.1]
    positivity
  have hscalar0 : 0 ≤ (1001 / 1000 : ℝ) ^ 2 * (C * (1001 / 1000) + 1 / 4) := by
    have hCp : 0 ≤ C := by linarith [hC.1]
    positivity
  have hratio : L ^ 2 / exp (L / 2) ≤ (144 / 40625 : ℝ) := by
    apply (div_le_iff₀ (exp_pos _)).mpr
    have he := exp_half_sharp hL
    nlinarith
  calc
    _ ≤ (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) *
        (2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) +
          log (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ)) := primepower_cost_envelope n hC hL
    _ ≤ (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) *
        ((C * (1001 / 1000 : ℝ) + 1 / 4) * L) := mul_le_mul_of_nonneg_left hinner hp0
    _ ≤ ((1001 / 1000 : ℝ) ^ 2 * L / exp (L / 2)) *
        ((C * (1001 / 1000 : ℝ) + 1 / 4) * L) :=
      mul_le_mul_of_nonneg_right (prefactor_bound hC hL) hinner0
    _ = ((1001 / 1000 : ℝ) ^ 2 * (C * (1001 / 1000) + 1 / 4)) *
        (L ^ 2 / exp (L / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio hscalar0

theorem primepower_cost_family (n : ℕ) {C : ℝ} (hC : C ∈ Icc (103 / 100 : ℝ) 16) :
    EvenKernel.PrimePowerCost n C (29 / 500) := by
  intro L hL
  have h := primepower_cost_scalar n hC hL
  have hm := mul_le_mul_of_nonneg_left hC.2
    (by norm_num : (0 : ℝ) ≤ (1001 / 1000) ^ 3 * (144 / 40625))
  nlinarith

theorem primepower_cost_215 : EvenKernel.PrimePowerCost 4 (43 / 20) (31 / 2000) := by
  intro L hL
  have h := primepower_cost_scalar 4 (by norm_num : (43 / 20 : ℝ) ∈ Icc (103 / 100) 16) hL
  norm_num at h ⊢
  linarith

#print axioms primepower_cost_envelope
#print axioms primepower_cost_scalar
#print axioms primepower_cost_family
#print axioms primepower_cost_215
end RHLimit.OcticPrimePowers
