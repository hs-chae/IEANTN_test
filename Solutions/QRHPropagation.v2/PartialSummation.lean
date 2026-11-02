/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Frontier

/-! A smaller pi coefficient, with the old600 cutoff reduced to300. -/
namespace QRHPhase2
open Real MeasureTheory Set IEANTN
open DudekPlattNumerics.Calculus
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le)

theorem pi_density_300 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eπ 0.01323 0 (7 / 8) (exp 300) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  let L := log x
  have hL : 300 ≤ L := by
    have hh := log_le_log (exp_pos (300 : ℝ)) hx
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  have hLne := hLpos.ne'
  have heq : exp L = x := exp_log hx0
  have hs : 2 ≤ exp (3 * L / 4) := by linarith [add_one_le_exp (3 * L / 4)]
  have hsx : exp (3 * L / 4) ≤ exp L := exp_le_exp.mpr (by linarith)
  have htail : HasPowerLogBound Eθ (((16 / 9 : ℝ) * 0.01714) / L ^ 2)
      2 (7 / 8) (exp (3 * L / 4)) := by
    intro t ht
    have ht0 : 0 < t := (exp_pos (3 * L / 4)).trans_le ht
    have hlog : 3 * L / 4 ≤ log t := by
      have hh := log_le_log (exp_pos (3 * L / 4)) ht
      simpa only [log_exp] using hh
    have hlogs : (3 * L / 4) ^ 2 ≤ log t ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlog 2
    have hcoef : (0.01714 : ℝ) ≤
        (((16 / 9 : ℝ) * 0.01714) / L ^ 2) * log t ^ 2 := by
      rw [show (((16 / 9 : ℝ) * 0.01714) / L ^ 2) * log t ^ 2 =
        (((16 / 9 : ℝ) * 0.01714) * log t ^ 2) / L ^ 2 from by ring]
      apply (le_div_iff₀ (pow_pos hLpos 2)).mpr
      nlinarith
    have hpoint := theta_192 hpsi t
      ((exp_le_exp.mpr (by linarith : (192 : ℝ) ≤ 3 * L / 4)).trans ht)
    simp only [pow_zero, mul_one] at hpoint
    exact hpoint.trans (mul_le_mul_of_nonneg_right hcoef (rpow_pos_of_pos ht0 _).le)
  have hi := QRHPiPower.error_integral_bound
    (A := (((16 / 9 : ℝ) * 0.01714) / L ^ 2)) (β := (7 / 8 : ℝ))
    (by positivity) (by norm_num) hs hsx htail
  rw [rpow_def_of_pos (exp_pos L), log_exp] at hi
  have hseven : exp (L * (7 / 8 : ℝ)) = exp (7 * L / 8) := by congr 1; ring
  rw [hseven] at hi
  have hp := QRHDensityApplications.pi_from_error_integral
    (show 2 ≤ exp L by linarith [add_one_le_exp L])
  rw [log_exp] at hp
  have hpoint := theta_300 hpsi (exp L)
    (exp_le_exp.mpr (by linarith : (300 : ℝ) ≤ L))
  rw [pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp] at hpoint
  have hpow : exp (L * ((7 / 8 : ℝ) - 1)) = exp (-L / 8) := by congr 1; ring
  rw [hpow] at hpoint
  have hnorm : Eπ (exp L) ≤
      ((0.01311 : ℝ) + (128 * 0.01714) / (63 * L)) * exp (-L / 8) +
        7 * L * exp (-L / 4) := by
    calc
      _ ≤ (0.01311 : ℝ) * exp (-L / 8) + L / exp L *
          (3 + (4 * exp (3 * L / 4) +
            (((16 / 9 : ℝ) * 0.01714) / L ^ 2) / (7 / 8) * exp (7 * L / 8))) :=
        hp.trans (add_le_add hpoint
          (mul_le_mul_of_nonneg_left (show 3 + |errorIntegral (exp L)| ≤
            3 + (4 * exp (3 * L / 4) +
              (((16 / 9 : ℝ) * 0.01714) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) by
            linarith [hi]) (by positivity)))
      _ ≤ (0.01311 : ℝ) * exp (-L / 8) + L / exp L *
          (7 * exp (3 * L / 4) +
            (((16 / 9 : ℝ) * 0.01714) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) := by
        have hh : 1 ≤ exp (3 * L / 4) := by
          linarith [add_one_le_exp (3 * L / 4)]
        have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ L / exp L by positivity)
        linarith
      _ = _ := by
        have hh : exp (3 * L / 4) = exp L * exp (-L / 4) := by
          rw [← exp_add]; congr 1; ring
        have hq : exp (7 * L / 8) = exp L * exp (-L / 8) := by
          rw [← exp_add]; congr 1; ring
        rw [hh, hq]
        field_simp
        ring
  have hd := poly_exp_decreasing 1 (L0 := (300 : ℝ)) (c := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hsdec : L * exp (-L / 8) ≤ (300 : ℝ) / 2 ^ 30 := by
    calc
      _ ≤ 300 * exp (-(75 / 2 : ℝ)) := by
        convert hd using 1 <;> congr 1 <;> ring
      _ ≤ 300 * exp (-(30 : ℝ)) := by gcongr; norm_num
      _ ≤ _ := by nlinarith [exp_neg_nat_le 30]
  have hearly : 7 * L * exp (-L / 4) ≤
      (2100 / (2 : ℝ) ^ 30) * exp (-L / 8) := by
    rw [show -L / 4 = -L / 8 + (-L / 8) from by ring, exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hsdec (exp_pos (-L / 8)).le]
  have hfrac : (128 * 0.01714 : ℝ) / (63 * L) ≤ (128 * 0.01714) / (63 * 300) := by
    gcongr
  have hcoef : (0.01311 : ℝ) + (128 * 0.01714) / (63 * L) +
      2100 / (2 : ℝ) ^ 30 ≤ 0.01323 := by
    norm_num at hfrac ⊢
    linarith
  have hfinal : Eπ (exp L) ≤ (0.01323 : ℝ) * exp (-L / 8) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef (exp_pos (-L / 8)).le]
  rw [← heq, pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp, hpow]
  exact hfinal

end QRHPhase2
