/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PartialSummation

/-! One more native integration-by-parts step removes the old coarse remainder loss. -/
namespace QRHPhase2
open Real MeasureTheory Set IEANTN
open DudekPlattNumerics.Calculus
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le hlog2_proof)

theorem I7_phase2_bound {x : ℝ} (hx : 4 ≤ x) :
    logIntegral 7 x ≤ x / log x ^ 7 + 7 * x / log x ^ 8 +
      56 * (sqrt x / log 2 ^ 9 + 512 * x / log x ^ 9) := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h6 := logIntegral_recurrence 6 (show 2 ≤ x by linarith)
  have h7 := logIntegral_recurrence 7 (show 2 ≤ x by linarith)
  have h9 := logIntegral_sqrt_bound 9 hx
  norm_num at h6 h7 h9
  have hp7 : 0 ≤ 2 / log (2 : ℝ) ^ 7 := by positivity
  have hp8 : 0 ≤ 2 / log (2 : ℝ) ^ 8 := by positivity
  calc
    _ = x / log x ^ 7 - 2 / log 2 ^ 7 + 7 * logIntegral 8 x := h6
    _ ≤ x / log x ^ 7 + 7 * (x / log x ^ 8 + 8 * logIntegral 9 x) := by
      apply add_le_add (sub_le_self _ hp7)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [h7]
      gcongr
      exact sub_le_self _ hp8
    _ ≤ x / log x ^ 7 + 7 * (x / log x ^ 8 +
        8 * (sqrt x / log 2 ^ 9 + 512 * x / log x ^ 9)) := by gcongr
    _ = _ := by ring

theorem scalar_I7_phase2 {L : ℝ} (hL : 144 ≤ L) :
    720 * (1 / L + 7 / L ^ 2 +
      56 * (L ^ 6 * exp (-L / 2) / log 2 ^ 9 + 512 / L ^ 3)) < 13 := by
  have hLpos : 0 < L := by linarith
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hd := poly_exp_decreasing 6 (L0 := (144 : ℝ)) (c := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hL
  have he : L ^ 6 * exp (-L / 2) ≤ (144 : ℝ) ^ 6 / 2 ^ 72 := by
    calc
      _ ≤ (144 : ℝ) ^ 6 * exp (-(72 : ℝ)) := by
        convert hd using 1 <;> congr 1 <;> ring
      _ ≤ _ := by nlinarith [exp_neg_nat_le 72]
  have hlogpow : (1 : ℝ) / log 2 ^ 9 ≤ (3 / 2 : ℝ) ^ 9 := by
    rw [show (1 : ℝ) / log 2 ^ 9 = (1 / log 2) ^ 9 by rw [div_pow]; ring]
    exact pow_le_pow_left₀ (by positivity) DudekPlattNumerics.v4.Numerics.inv_log2_lt.le 9
  have hn : L ^ 6 * exp (-L / 2) / log 2 ^ 9 ≤
      ((144 : ℝ) ^ 6 / 2 ^ 72) * (3 / 2 : ℝ) ^ 9 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul he hlogpow (by positivity) (by positivity)
  have h1 : (1 : ℝ) / L ≤ 1 / 144 := by gcongr
  have h2 : (7 : ℝ) / L ^ 2 ≤ 7 / 144 ^ 2 := by gcongr
  have h3 : (512 : ℝ) / L ^ 3 ≤ 512 / 144 ^ 3 := by gcongr
  have hnum : (720 : ℝ) * (1 / 144 + 7 / 144 ^ 2 +
      56 * (((144 : ℝ) ^ 6 / 2 ^ 72) * (3 / 2 : ℝ) ^ 9 + 512 / 144 ^ 3)) < 13 := by
    norm_num
  linarith

theorem normalized_I7_phase2 {L : ℝ} (hL : 144 ≤ L) :
    L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) < 13 := by
  have hLpos : 0 < L := by linarith
  have hb := I7_phase2_bound (show 4 ≤ exp L by linarith [add_one_le_exp L])
  have hhalf : exp (L / 2) = exp L * exp (-L / 2) := by
    rw [← exp_add]; congr 1; ring
  calc
    _ ≤ L ^ 6 / exp L * (720 * (exp L / log (exp L) ^ 7 +
        7 * exp L / log (exp L) ^ 8 +
        56 * (sqrt (exp L) / log 2 ^ 9 + 512 * exp L / log (exp L) ^ 9))) := by gcongr
    _ = 720 * (1 / L + 7 / L ^ 2 +
        56 * (L ^ 6 * exp (-L / 2) / log 2 ^ 9 + 512 / L ^ 3)) := by
      rw [log_exp, ← exp_half, hhalf]
      field_simp
      <;> ring
    _ < _ := scalar_I7_phase2 hL

theorem scalar_A_phase2 {L : ℝ} (hL : 144 ≤ L) :
    2 * DudekPlattNumerics.Calculus.A * L ^ 6 * exp (-L) < 1 := by
  have hL0 : (0 : ℝ) < 144 := by norm_num
  have h1 : L ^ 6 * Real.exp (-(1:ℝ) * L) ≤ (144:ℝ) ^ 6 * Real.exp (-(1:ℝ) * 144) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have he : Real.exp (-(1:ℝ) * L) = Real.exp (-L) := by congr 1; ring
  have he2 : Real.exp (-(1:ℝ) * (144:ℝ)) = Real.exp (-(144:ℕ) : ℝ) := by
    congr 1; push_cast; ring
  rw [he, he2] at h1
  have hAnn : (0:ℝ) ≤ A := by
    have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
    unfold A; positivity
  have hAb : DudekPlattNumerics.Calculus.A < 1600 :=
    DudekPlattNumerics.v4.Numerics.A_lt
  -- avoid the huge-exponent evaluator threshold: reduce -144 to a safely negligible -100 first
  have hexp144 : Real.exp (-(144:ℕ) : ℝ) ≤ 1 / 2 ^ (100:ℕ) := by
    calc Real.exp (-(144:ℕ) : ℝ) ≤ Real.exp (-(100:ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr; norm_num
      _ ≤ 1 / 2 ^ (100:ℕ) := exp_neg_nat_le 100
  have hstep : 2 * A * (L ^ 6 * Real.exp (-L)) ≤
      2 * 1600 * ((144:ℝ) ^ 6 * (1 / 2 ^ (100:ℕ))) := by
    calc 2 * A * (L ^ 6 * Real.exp (-L))
        ≤ 2 * A * ((144:ℝ) ^ 6 * Real.exp (-(144:ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * 1600 * ((144:ℝ) ^ 6 * Real.exp (-(144:ℕ) : ℝ)) := by gcongr
      _ ≤ 2 * 1600 * ((144:ℝ) ^ 6 * (1 / 2 ^ (100:ℕ))) := by gcongr
  have hfin : (2 * 1600 * ((144:ℝ) ^ 6 * (1 / 2 ^ (100:ℕ))) : ℝ) < 1 := by
    norm_num
  nlinarith [hstep, hfin]


end QRHPhase2
