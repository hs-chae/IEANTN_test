/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Terence Tao and IEANTN contributors; adapted in this study.
-/
import Section7Vihuela
open Real MeasureTheory Set
namespace Loose7
open CH2Section7 CH2Section7T CH2Section7A
set_option maxHeartbeats 2000000 in
theorem vihuela (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (11.1404 : ℝ))
    {T σ ξ : ℝ} (hT : (10 : ℝ) ^ 7 - 1 ≤ T) (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → z.im ≠ T) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hξ : |ξ| ≤ 1) :
    2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 T)
        (fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
      ≤ 1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
        - 1.001 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) + 0.821 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hT0 : (0 : ℝ) < T := by linarith [show (0:ℝ) < 10 ^ 7 by norm_num]
  have hs : |σ - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hσT : |σ - 1 / 2| ≤ T / 2 := by linarith
  set t₀ : ℝ := 20000 with ht₀
  rw [zsum_split (a := t₀) (by norm_num) (by rw [ht₀]; linarith), mul_add]
  have hsal := salmon hcs hrvm hsmall hRH (t₀ := t₀) (by norm_num) (by rw [ht₀]; linarith)
    hσ1.ne hσT hξ
  have had := adar hcs hrvm hsmall hRH hTfree (t₀ := t₀) (by norm_num) (by rw [ht₀]; linarith)
    hσ1.ne hσT hξ
  have hP : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun ρ ↦ 1 / ρ.im) ≤ 11.1404 := hplatt
  -- the numbers
  obtain ⟨hL0lo, hL0hi⟩ := log_t0_bounds
  rw [← ht₀] at hL0lo hL0hi
  have hC1 := C1lo_twelve
  have hC2 := C2hi_le
  set y := Real.log (T / (2 * Real.pi)) with hy
  set L0 := Real.log (t₀ / (2 * Real.pi)) with hL0
  -- `y ≤ log(10⁷/2π) + T/10⁷ - 1`
  have hylog : y ≤ 14.3 + T / 10 ^ 7 - 1 := by
    have h1 : y = Real.log ((10 : ℝ) ^ 7 / (2 * Real.pi)) + Real.log (T / 10 ^ 7) := by
      rw [hy, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h2 := Real.log_le_sub_one_of_pos (show 0 < T / 10 ^ 7 by positivity)
    linarith [log_T0_le]
  have hy0 : 0 ≤ y := by
    rw [hy]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hu : 1 / T ≤ 1.0000002e-7 := by rw [div_le_iff₀ hT0]; norm_num; linarith
  have hu0 : 0 < 1 / T := by positivity
  -- each error term
  have hlogTt0 : Real.log (T / t₀) ≤ T / 10 ^ 7 + 5.22 := by
    have h1 : Real.log (T / t₀) = Real.log (T / 10 ^ 7) + Real.log 500 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; rw [ht₀]; field_simp; norm_num
    have h2 := Real.log_le_sub_one_of_pos (show 0 < T / 10 ^ 7 by positivity)
    linarith [log_500_le]
  have hlog20000 := log_20000_le
  rw [← ht₀] at hlog20000
  have hLe : Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) ≤ 9.07 := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith
  have hLe0 : 0 ≤ Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; nlinarith [Real.exp_one_gt_d9]
  have hlog0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by norm_num)
  have hL0nn : 0 ≤ L0 := by linarith
  have hc' : 2.78 * |σ - 1 / 2| + 1 ≤ 2.39 := by linarith
  have hc'0 : 0 ≤ 2.78 * |σ - 1 / 2| + 1 := by positivity
  -- salmon's error
  have hE1 : t₀ / T * (1 + (2.78 * |σ - 1 / 2| + 1) / T) * L0 ≤ 0.016141 := by
    have ha : t₀ / T ≤ 0.0020001 := by rw [ht₀, div_le_iff₀ hT0]; linarith
    have hb : (2.78 * |σ - 1 / 2| + 1) / T ≤ 2.3901e-7 := by
      rw [div_le_iff₀ hT0]; nlinarith
    have hb0 : 0 ≤ (2.78 * |σ - 1 / 2| + 1) / T := by positivity
    have : t₀ / T * (1 + (2.78 * |σ - 1 / 2| + 1) / T) ≤ 0.0020001 * (1 + 2.3901e-7) := by
      apply mul_le_mul ha (by linarith) (by positivity) (by norm_num)
    calc _ ≤ 0.0020001 * (1 + 2.3901e-7) * 8.07 := mul_le_mul this hL0hi hL0nn (by norm_num)
      _ ≤ 0.016141 := by norm_num
  have hE2 : 14 * (y + 1) * (t₀ / T) ^ 2 ≤ 0.001 := by
    have h1 : (y + 1) * (1 / T) ≤ 15.31e-7 := by
      have : (y + 1) * (1 / T) ≤ (14.3 + T / 10 ^ 7) * (1 / T) :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have e : (14.3 + T / 10 ^ 7) * (1 / T) = 14.3 * (1 / T) + 1e-7 := by field_simp; ring
      nlinarith
    have e : 14 * (y + 1) * (t₀ / T) ^ 2 = 14 * ((y + 1) * (1 / T)) * (t₀ ^ 2 * (1 / T)) := by
      field_simp
    rw [e]
    have h2 : t₀ ^ 2 * (1 / T) ≤ 40.0001 := by rw [ht₀]; nlinarith
    have h3 : 0 ≤ (y + 1) * (1 / T) := by positivity
    calc 14 * ((y + 1) * (1 / T)) * (t₀ ^ 2 * (1 / T)) ≤ 14 * 15.31e-7 * 40.0001 := by gcongr
      _ ≤ 0.001 := by norm_num
  have hE3 : 2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T) ≤ 0.000031 := by
    have h1 : Real.log (T / t₀) * (1 / T) ≤ 1.0000002e-7 + 5.2200011e-7 := by
      have hlp : 0 ≤ Real.log (T / t₀) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
      have : Real.log (T / t₀) * (1 / T) ≤ (T / 10 ^ 7 + 5.22) * (1 / T) :=
        mul_le_mul_of_nonneg_right hlogTt0 hu0.le
      have e : (T / 10 ^ 7 + 5.22) * (1 / T) = 1e-7 + 5.22 * (1 / T) := by field_simp; ring
      nlinarith
    have e : 2 * Real.pi * Real.log (T / t₀) / (5 * T) = 2 * Real.pi / 5 * (Real.log (T / t₀) * (1 / T)) := by
      field_simp
    rw [e, ht₀]
    have hl0 : 0 ≤ Real.log (T / 20000) * (1 / T) := by
      apply mul_nonneg _ hu0.le; apply Real.log_nonneg; rw [le_div_iff₀ (by norm_num)]; linarith
    rw [ht₀] at h1
    nlinarith
  have hE4 : (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) ≤ 0.000802 := by
    have h1 : 2 * Real.pi / T ≤ 6.3e-7 := by
      rw [div_le_iff₀ hT0]; nlinarith
    have h2 : 2 * Real.log t₀ / 5 + 4 ≤ 7.968 := by linarith
    have h3 : 2 / t₀ + 2 * Real.pi / T ≤ 0.0001 + 6.3e-7 := by rw [ht₀]; norm_num; linarith
    calc _ ≤ (0.0001 + 6.3e-7) * 7.968 := mul_le_mul h3 h2 (by positivity) (by norm_num)
      _ ≤ 0.000802 := by norm_num
  have hE5 : 2 * |σ - 1 / 2| * (Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
      + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2) ≤ 0.0000723 := by
    have h1 : Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀) ≤ 9.07 / (2 * 3.141592 * 20000) := by
      rw [ht₀]; rw [ht₀] at hLe hLe0
      apply div_le_div₀ (by norm_num) hLe (by positivity); nlinarith
    have h2 : (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 ≤ 8.07 / 20000 ^ 2 := by
      rw [ht₀]; rw [ht₀] at hlog20000
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have h3 : 2 * |σ - 1 / 2| ≤ 1 := by linarith
    have h4 : 0 ≤ Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
        + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 := by positivity
    calc _ ≤ 1 * (9.07 / (2 * 3.141592 * 20000) + 8.07 / 20000 ^ 2) :=
          mul_le_mul h3 (by linarith) h4 (by norm_num)
      _ ≤ 0.0000723 := by norm_num
  have hE6 : (2.78 * |σ - 1 / 2| + 1) * y / T ≤ 0.0000037 := by
    have h1 : y * (1 / T) ≤ 14.31e-7 := by
      have : y * (1 / T) ≤ (13.3 + T / 10 ^ 7) * (1 / T) :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have e : (13.3 + T / 10 ^ 7) * (1 / T) = 13.3 * (1 / T) + 1e-7 := by field_simp; ring
      nlinarith
    have e : (2.78 * |σ - 1 / 2| + 1) * y / T = (2.78 * |σ - 1 / 2| + 1) * (y * (1 / T)) := by
      field_simp
    rw [e]
    have : 0 ≤ y * (1 / T) := by positivity
    calc _ ≤ 2.39 * 14.31e-7 := mul_le_mul hc' h1 this (by norm_num)
      _ ≤ 0.0000037 := by norm_num
  -- the main terms
  have hmain : (1 / (2 * Real.pi)) * (y ^ 2 - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
      + 14 * (y + 1) * (t₀ / T) ^ 2) + 10.3194
      ≤ 1 / (2 * Real.pi) * y ^ 2 - 1.001 / (6 * Real.pi) * y
        - (0.016141 + 0.000031 + 0.000802 + 0.0000723 + 0.0000037) := by
    have hL0sq : 65.028 ≤ L0 ^ 2 := by nlinarith
    have hkey : (1 / (2 * Real.pi)) * (- L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
        + 14 * (y + 1) * (t₀ / T) ^ 2) + 10.3194
        ≤ - 1.001 / (6 * Real.pi) * y - 0.01705 := by
      rw [show - 1.001 / (6 * Real.pi) * y = (1 / (2 * Real.pi)) * (-(1.001 / 3) * y) by
        field_simp; ring]
      have hA : - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi + 14 * (y + 1) * (t₀ / T) ^ 2
          ≤ -(1.001 / 3) * y - 2 * Real.pi * (10.3194 + 0.01705) := by
        have hy' : 0 ≤ (2 * C1lo 12 - 1.001 / 3) * y := by
          apply mul_nonneg _ hy0; linarith
        nlinarith
      have := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
      have e : 1 / (2 * Real.pi) * (-(1.001 / 3) * y - 2 * Real.pi * (10.3194 + 0.01705))
          = 1 / (2 * Real.pi) * (-(1.001 / 3) * y) - (10.3194 + 0.01705) := by
        field_simp
      linarith
    have e : (1 / (2 * Real.pi)) * (y ^ 2 - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
        + 14 * (y + 1) * (t₀ / T) ^ 2)
        = 1 / (2 * Real.pi) * y ^ 2 + (1 / (2 * Real.pi)) * (- L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
          + 14 * (y + 1) * (t₀ / T) ^ 2) := by ring
    rw [e]
    have : 0.01705 ≥ (0.016141 + 0.000031 + 0.000802 + 0.0000723 + 0.0000037 : ℝ) := by norm_num
    have hneg : -1.001 / (6 * Real.pi) * y = -(1.001 / (6 * Real.pi) * y) := by ring
    rw [hneg] at hkey
    set Z := 1.001 / (6 * Real.pi) * y
    set X := 1 / (2 * Real.pi) * (-L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi + 14 * (y + 1) * (t₀ / T) ^ 2)
    linarith
  linarith [hsal, had, hP, hE1, hE2, hE3, hE4, hE5, hE6, hmain]


end Loose7
