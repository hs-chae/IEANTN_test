/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityRemainder
import NumericEnvelope

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Common admissibility estimates for every selected row height, throughout its entire range of x. -/
theorem density_height_parameters {k x : ℝ} (hx0 : 0 < x) (hL : 64 ≤ Real.log x)
    (hk : k ≤ 7 / 10) (hsep : 34 ≤ k * Real.log x - Real.log x / 8) :
    let T := Real.exp (k * Real.log x) + 1 / 2
    3 * (10 : ℝ) ^ (12 : ℕ) + 1 ≤ T ∧ 16 ≤ Real.log T ∧
      1000000 ≤ x ∧ Real.log T ≤ (3 / 4) * Real.log x ∧
        T / x ≤ (1 : ℝ) / 1000000 ∧
          Real.log T ≤ k * Real.log x + (1 : ℝ) / 10 ^ (9 : ℕ) := by
  let R := k * Real.log x
  let T := Real.exp R + 1 / 2
  have hR : 42 ≤ R := by dsimp [R]; linarith
  have he42 : (10 : ℝ) ^ (18 : ℕ) ≤ Real.exp 42 := by
    have hh := (CH2Section7A.exp_nat_bounds 42).1
    norm_num at hh ⊢; linarith
  have heR : (10 : ℝ) ^ (18 : ℕ) ≤ Real.exp R :=
    he42.trans (Real.exp_le_exp.mpr hR)
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hTlo : 3 * (10 : ℝ) ^ (12 : ℕ) + 1 ≤ T := by dsimp [T]; norm_num at heR ⊢; linarith
  have hlogTlo : 16 ≤ Real.log T := by
    have hh : Real.exp 16 ≤ T := by
      exact (Real.exp_le_exp.mpr (by linarith : (16 : ℝ) ≤ R)).trans (by dsimp [T]; linarith)
    have hh' := Real.log_le_log (Real.exp_pos (16 : ℝ)) hh
    simpa using hh'
  have hxlo : 1000000 ≤ x := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have he16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    exact he16.trans ((Real.exp_le_exp.mpr (by linarith : (16 : ℝ) ≤ Real.log x)).trans_eq (Real.exp_log hx0))
  have hlogextra : Real.log T ≤ R + (1 : ℝ) / 10 ^ (9 : ℕ) := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < T / Real.exp R by positivity)
    rw [Real.log_div hT0.ne' (Real.exp_pos R).ne', Real.log_exp] at hh
    have he : T / Real.exp R - 1 = (1 / 2 : ℝ) / Real.exp R := by dsimp [T]; field_simp; ring
    rw [he] at hh
    have hi : (1 / 2 : ℝ) / Real.exp R ≤ (1 : ℝ) / 10 ^ (9 : ℕ) := by
      apply (div_le_iff₀ (Real.exp_pos R)).mpr
      norm_num at heR ⊢; linarith
    linarith
  have hlogT : Real.log T ≤ (3 / 4) * Real.log x := by
    have hl0 : 0 ≤ Real.log x := by linarith
    have hh := mul_le_mul_of_nonneg_right hk hl0
    dsimp [R] at hlogextra
    linarith
  have hquot : (1000000 : ℝ) ≤ x / T := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have he16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    calc
      (1000000 : ℝ) ≤ Real.exp 16 := he16
      _ ≤ Real.exp (Real.log x - Real.log T) := Real.exp_le_exp.mpr (by linarith)
      _ = x / T := by rw [Real.exp_sub, Real.exp_log hx0, Real.exp_log hT0]
  have hTdiv : T / x ≤ (1 : ℝ) / 1000000 := by
    have hh := (le_div_iff₀ hT0).mp hquot
    rw [div_le_iff₀ hx0]; nlinarith
  exact ⟨hTlo, hlogTlo, hxlo, hlogT, hTdiv, hlogextra⟩

/-- All non-spectral error terms contribute less than 10^-12 to any row coefficient. -/
theorem density_remainder_coefficient {k x : ℝ} (hx0 : 0 < x) (hL : 64 ≤ Real.log x)
    (hk : k ≤ 7 / 10) (hsep : 34 ≤ k * Real.log x - Real.log x / 8) :
    finiteRemainder (Real.exp (k * Real.log x) + 1 / 2) x * x ^ ((1 : ℝ) / 8) ≤
      (1 : ℝ) / 10 ^ (12 : ℕ) := by
  let T := Real.exp (k * Real.log x) + 1 / 2
  obtain ⟨hTlo, _, hxlo, hlogT, hTdiv, _⟩ := density_height_parameters hx0 hL hk hsep
  have hT0 : 0 < T := by dsimp [T]; positivity
  have hscaled := density_scaled_remainder
    (by dsimp [T]; norm_num at hTlo ⊢; linarith : 1000000 ≤ T) hxlo hL hlogT hTdiv
  have hratio : x ^ ((1 : ℝ) / 8) / T ≤ Real.exp (-34) := by
    calc
      _ ≤ x ^ ((1 : ℝ) / 8) / Real.exp (k * Real.log x) := by dsimp [T]; gcongr; linarith
      _ = Real.exp (Real.log x / 8 - k * Real.log x) := by
        rw [Real.rpow_def_of_pos hx0, Real.exp_sub]; congr 2; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hT0).mpr hscaled)
    (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 8)).le
  have h34 := (CH2Section7A.exp_nat_bounds 34).1
  have he : (3.2 : ℝ) * Real.exp (-34) ≤ (1 : ℝ) / 10 ^ (12 : ℕ) := by
    rw [Real.exp_neg, ← one_div, mul_one_div, div_le_iff₀ (Real.exp_pos (34 : ℝ))]
    norm_num at h34 ⊢; linarith
  have hr := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 3.2)
  change finiteRemainder T x * x ^ ((1 : ℝ) / 8) ≤ _
  convert (hmul.trans (by convert hr.trans he using 1 <;> ring)) using 1

end CH2QRH
