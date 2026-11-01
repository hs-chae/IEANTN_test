/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PiPower
import IEANTN.Nodes.QRHCH2.v2.Conclusions

/-! Log-free theta, pi and prime-interval consequences of the already proved density frontier. -/
namespace QRHDensityApplications
open Real MeasureTheory Set IEANTN
open DudekPlattNumerics.Calculus
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le)

theorem theta_density (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasPowerLogBound Eθ (1 / 50) 0 (7 / 8) (exp 300) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  let L := log x
  have hL : 300 ≤ L := by
    have hh := log_le_log (exp_pos (300 : ℝ)) hx
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  have heq : exp L = x := exp_log hx0
  have hψ := hpsi 300 0.01310 (by norm_num [CH2.v6.densityFrontier]) (exp L)
    (exp_le_exp.mpr hL)
  rw [rpow_def_of_pos (exp_pos L), log_exp] at hψ
  have he1 : exp (L * (-(1 : ℝ) / 8)) = exp (-L / 8) := by congr 1; ring
  rw [he1] at hψ
  have hc := div_le_div_of_nonneg_right
    (Chebyshev.psi_sub_theta_le (show 1 ≤ exp L by linarith [add_one_le_exp L]))
    (exp_pos L).le
  rw [← exp_half, log_exp] at hc
  have hratio : exp (L / 2) / exp L = exp (-L / 2) := by
    rw [← exp_sub]; congr 1; ring
  have hc' : (Chebyshev.psi (exp L) - Chebyshev.theta (exp L)) / exp L ≤
      2 * L * exp (-L / 2) := by
    calc
      _ ≤ (2 * exp (L / 2) * L) / exp L := hc
      _ = 2 * L * (exp (L / 2) / exp L) := by ring
      _ = _ := by rw [hratio]
  have hd := poly_exp_decreasing 1 (L0 := (300 : ℝ)) (c := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hid : -(3 / 8 : ℝ) * L = -3 * L / 8 := by ring
  rw [hid] at hd
  norm_num at hd
  have hExp : exp (-(225 / 2 : ℝ)) ≤ 1 / (2 : ℝ) ^ 100 := by
    calc
      _ ≤ exp (-(100 : ℕ)) := exp_le_exp.mpr (by norm_num)
      _ ≤ _ := exp_neg_nat_le 100
  have hs : L * exp (-3 * L / 8) ≤ (300 : ℝ) / 2 ^ 100 := by
    calc
      _ ≤ 300 * exp (-(225 / 2 : ℝ)) := by
        convert hd using 1 <;> congr 1 <;> ring
      _ ≤ _ := by nlinarith [hExp]
  have hcorr : 2 * L * exp (-L / 2) ≤ (600 / (2 : ℝ) ^ 100) * exp (-L / 8) := by
    rw [show -L / 2 = -3 * L / 8 + (-L / 8) from by ring, exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hs (exp_pos (-L / 8)).le]
  have ht := FKS2Sol.Etheta_le_Epsi_add (exp_pos L)
  have hcoeff : (0.01310 : ℝ) + 600 / 2 ^ 100 ≤ 1 / 50 := by norm_num
  have hfin : Eθ (exp L) ≤ (1 / 50 : ℝ) * exp (-L / 8) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (exp_pos (-L / 8)).le]
  rw [← heq, pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp]
  have hid' : exp (L * ((7 / 8 : ℝ) - 1)) = exp (-L / 8) := by congr 1; ring
  rw [hid']
  exact hfin

theorem intervals_density
    (hθ : HasPowerLogBound Eθ (1 / 50) 0 (7 / 8) (exp 300))
    (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∀ x ≥ exp 300, HasPrimeInInterval x ((2 / 25 : ℝ) * x ^ ((7 : ℝ) / 8)) := by
  have hs : (1 / 50 : ℝ) * (300 : ℝ) ^ 0 * exp (-(1 - 7 / 8) * 300) ≤ 1 / 4 := by
    have he : exp (-(1 - (7 / 8 : ℝ)) * 300) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
    norm_num only [pow_zero, mul_one]
    nlinarith [he]
  have hp := QRHPowerBounds.intervals_of_power hcrit (by norm_num : (0 : ℝ) < 1 / 50)
    (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : (0 : ℝ) < 300)
    (k := 0) (by norm_num) hs hθ
  intro x hx
  convert hp x hx using 1 <;> ring

/-- Native pointwise partial summation, before applying any particular envelope. -/
theorem pi_from_error_integral {x : ℝ} (hx : 2 ≤ x) :
    Eπ x ≤ Eθ x + log x / x * (3 + |errorIntegral x|) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc : 2 / log (2 : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hlog2]
    linarith [DudekPlattNumerics.v4.Numerics.hlog2_proof]
  have htri : |primeCounting x - Li x| ≤ |thetaError x| / log x + 3 + |errorIntegral x| := by
    rw [FKS2Sol.piMinusLi_eq hx]
    have h1 := abs_add_le ((Chebyshev.theta x - x) / log x + 2 / log 2)
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2))
    have h2 := abs_add_le ((Chebyshev.theta x - x) / log x) (2 / log 2)
    rw [abs_div, abs_of_pos hl, abs_of_nonneg (show 0 ≤ 2 / log (2 : ℝ) by positivity)] at h2
    dsimp [thetaError, errorIntegral] at *
    linarith
  have hs := mul_le_mul_of_nonneg_left htri (show 0 ≤ log x / x by positivity)
  have heq : log x / x * (|thetaError x| / log x + 3 + |errorIntegral x|) =
      Eθ x + log x / x * (3 + |errorIntegral x|) := by
    dsimp [Eθ, thetaError]
    field_simp
    ring
  unfold Eπ
  rw [div_div_eq_mul_div]
  calc
    _ = log x / x * |primeCounting x - Li x| := by ring
    _ ≤ _ := hs.trans_eq heq

theorem pi_density
    (hθ : HasPowerLogBound Eθ (1 / 50) 0 (7 / 8) (exp 300)) :
    HasPowerLogBound Eπ (21 / 1000) 0 (7 / 8) (exp 600) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (600 : ℝ)).trans_le hx
  let L := log x
  have hL : 600 ≤ L := by
    have hh := log_le_log (exp_pos (600 : ℝ)) hx
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  have hLne := hLpos.ne'
  have heq : exp L = x := exp_log hx0
  have hs : 2 ≤ exp (L / 2) := by linarith [add_one_le_exp (L / 2)]
  have hsx : exp (L / 2) ≤ exp L := exp_le_exp.mpr (by linarith)
  have htail : HasPowerLogBound Eθ ((2 / 25 : ℝ) / L ^ 2) 2 (7 / 8) (exp (L / 2)) := by
    intro t ht
    have ht0 : 0 < t := (exp_pos (L / 2)).trans_le ht
    have hlog : L / 2 ≤ log t := by
      have hh := log_le_log (exp_pos (L / 2)) ht
      simpa only [log_exp] using hh
    have hlogs : (L / 2) ^ 2 ≤ log t ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlog 2
    have hcoef : (1 / 50 : ℝ) ≤ ((2 / 25 : ℝ) / L ^ 2) * log t ^ 2 := by
      rw [show ((2 / 25 : ℝ) / L ^ 2) * log t ^ 2 =
        ((2 / 25 : ℝ) * log t ^ 2) / L ^ 2 from by ring]
      apply (le_div_iff₀ (pow_pos hLpos 2)).mpr
      nlinarith
    have hpoint := hθ t ((exp_le_exp.mpr (by linarith : (300 : ℝ) ≤ L / 2)).trans ht)
    simp only [pow_zero, mul_one] at hpoint
    exact hpoint.trans (mul_le_mul_of_nonneg_right hcoef (rpow_pos_of_pos ht0 _).le)
  have hi := QRHPiPower.error_integral_bound (A := ((2 / 25 : ℝ) / L ^ 2))
    (β := (7 / 8 : ℝ)) (by positivity) (by norm_num) hs hsx htail
  rw [rpow_def_of_pos (exp_pos L), log_exp] at hi
  have hseven : exp (L * (7 / 8 : ℝ)) = exp (7 * L / 8) := by congr 1; ring
  rw [hseven] at hi
  have hp := pi_from_error_integral (show 2 ≤ exp L by linarith [add_one_le_exp L])
  rw [log_exp] at hp
  have hpoint := hθ (exp L) (exp_le_exp.mpr (by linarith : (300 : ℝ) ≤ L))
  rw [pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp] at hpoint
  have hpow : exp (L * ((7 / 8 : ℝ) - 1)) = exp (-L / 8) := by congr 1; ring
  rw [hpow] at hpoint
  have hnorm : Eπ (exp L) ≤
      ((1 / 50 : ℝ) + 16 / (175 * L)) * exp (-L / 8) + 7 * L * exp (-L / 2) := by
    calc
      _ ≤ (1 / 50 : ℝ) * exp (-L / 8) + L / exp L *
          (3 + (4 * exp (L / 2) + ((2 / 25 : ℝ) / L ^ 2) / (7 / 8) * exp (7 * L / 8))) :=
        hp.trans (add_le_add hpoint
          (mul_le_mul_of_nonneg_left (show 3 + |errorIntegral (exp L)| ≤
            3 + (4 * exp (L / 2) + ((2 / 25 : ℝ) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) by
            linarith [hi]) (by positivity)))
      _ ≤ (1 / 50 : ℝ) * exp (-L / 8) + L / exp L *
          (7 * exp (L / 2) + ((2 / 25 : ℝ) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) := by
        have hh : 1 ≤ exp (L / 2) := by linarith [add_one_le_exp (L / 2)]
        have hsum : 3 + (4 * exp (L / 2) +
            ((2 / 25 : ℝ) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) ≤
            7 * exp (L / 2) + ((2 / 25 : ℝ) / L ^ 2) / (7 / 8) * exp (7 * L / 8) := by
          linarith
        have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ L / exp L by positivity)
        linarith
      _ = _ := by
        have hh : exp (L / 2) = exp L * exp (-L / 2) := by
          rw [← exp_add]; congr 1; ring
        have hq : exp (7 * L / 8) = exp L * exp (-L / 8) := by
          rw [← exp_add]; congr 1; ring
        rw [hh, hq]
        field_simp
        ring
  have hd := poly_exp_decreasing 1 (L0 := (600 : ℝ)) (c := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hsdec : L * exp (-3 * L / 8) ≤ (600 : ℝ) / 2 ^ 200 := by
    calc
      _ ≤ 600 * exp (-(225 : ℝ)) := by
        convert hd using 1 <;> congr 1 <;> ring
      _ ≤ 600 * exp (-(200 : ℝ)) := by gcongr; norm_num
      _ ≤ _ := by nlinarith [exp_neg_nat_le 200]
  have hearly : 7 * L * exp (-L / 2) ≤
      (4200 / (2 : ℝ) ^ 200) * exp (-L / 8) := by
    rw [show -L / 2 = -3 * L / 8 + (-L / 8) from by ring, exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hsdec (exp_pos (-L / 8)).le]
  have hfrac : (16 : ℝ) / (175 * L) ≤ 16 / (175 * 600) := by gcongr
  have hcoef : (1 / 50 : ℝ) + 16 / (175 * L) + 4200 / (2 : ℝ) ^ 200 ≤ 21 / 1000 := by
    norm_num at hfrac ⊢
    linarith
  have hfinal : Eπ (exp L) ≤ (21 / 1000 : ℝ) * exp (-L / 8) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef (exp_pos (-L / 8)).le]
  rw [← heq, pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp, hpow]
  exact hfinal

end QRHDensityApplications
