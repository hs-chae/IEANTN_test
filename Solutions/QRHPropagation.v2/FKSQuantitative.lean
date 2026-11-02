/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PartialSummation
import FKS2PipelineReplay

/-! Concrete classical coefficients and a certified existing FKS2 correction. -/
namespace QRHPhase2
open Real IEANTN FKS2.v2

theorem classical_of_logfree {E : ℝ → ℝ} {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hCA : C * (10 / 27 : ℝ) ^ 2 ≤ 90000 * A)
    (hE : HasPowerLogBound E C 0 (7 / 8) (exp 300)) :
    HasClassicalBound E A 2 2 1 (exp 300) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  let L := log x
  have hL : 300 ≤ L := by
    have h := log_le_log (exp_pos (300 : ℝ)) hx
    simpa [L] using h
  have hL0 : 0 ≤ L := by linarith
  have heq : exp L = x := exp_log hx0
  have hs := sq_sqrt hL0
  have hcut : 2 * sqrt L - L / 8 ≤ -2 := by
    nlinarith [sq_nonneg (sqrt L - 16)]
  have hratio : exp (2 * sqrt L - L / 8) ≤ (10 / 27 : ℝ) ^ 2 :=
    (exp_le_exp.mpr hcut).trans (QRHPropagation.exp_neg_nat_upper 2)
  have hsplit : exp (-L / 8) = exp (-2 * sqrt L) * exp (2 * sqrt L - L / 8) := by
    rw [← exp_add]; congr 1; ring
  have hcross : C * exp (-L / 8) ≤ (C * (10 / 27 : ℝ) ^ 2) * exp (-2 * sqrt L) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ C * exp (-2 * sqrt L) by positivity)
    nlinarith
  have hLsq : (90000 : ℝ) ≤ L ^ 2 := by nlinarith
  have hcoef : C * (10 / 27 : ℝ) ^ 2 ≤ A * L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hLsq hA]
  have hp := hE (exp L) (exp_le_exp.mpr hL)
  simp only [pow_zero, mul_one] at hp
  rw [rpow_def_of_pos (exp_pos L), log_exp,
    show L * ((7 / 8 : ℝ) - 1) = -L / 8 from by ring] at hp
  have hfinal : E (exp L) ≤ A * L ^ 2 * exp (-2 * sqrt L) :=
    hp.trans (hcross.trans (mul_le_mul_of_nonneg_right hcoef (exp_pos _).le))
  rw [← heq]
  simpa only [admissibleBound, log_exp, div_one, rpow_two, ← sqrt_eq_rpow, neg_mul] using hfinal

theorem dawson_le_one {v : ℝ} (hv : 3 ≤ v) : dawson v ≤ 1 := by
  have hb := FKS2Sol.dawson_le (show 2 ≤ v by linarith)
  have he : exp (4 - v ^ 2) ≤ (10 / 27 : ℝ) ^ 5 :=
    (exp_le_exp.mpr (by nlinarith : 4 - v ^ 2 ≤ -5)).trans
      (QRHPropagation.exp_neg_nat_upper 5)
  have hf : (4 : ℝ) / (7 * v) ≤ 4 / 21 := by gcongr; linarith
  have hn : (2 : ℝ) * (10 / 27 : ℝ) ^ 5 + 4 / 21 ≤ 1 := by norm_num
  linarith

theorem mu_300_le (hpsi : QRHCH2.v2.psi_density_frontier) :
    muAsymp 0.0000001 2 2 1 (exp 300) (exp 300) ≤ 0.6 := by
  let X := exp (300 : ℝ)
  let d := (0.0000001 : ℝ) * 300 ^ 2 * exp (-2 * sqrt (300 : ℝ))
  have hX : 0 < X := exp_pos _
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 17 ≤ sqrt (300 : ℝ) := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 300), sqrt_nonneg (300 : ℝ)]
  have heq : muAsymp 0.0000001 2 2 1 (exp 300) (exp 300) =
      |(primeCounting X - Li X) / (X / 300) - (Chebyshev.theta X - X) / X| / d +
        2 * dawson (sqrt (300 : ℝ) - 1) / sqrt (300 : ℝ) := by
    dsimp [X, d, muAsymp, admissibleBound]
    simp only [log_exp, div_one, rpow_two, ← sqrt_eq_rpow, sqrt_one, mul_one]
    norm_num only
    field_simp
  have ht := theta_300 hpsi X le_rfl
  have hp := pi_density_300 hpsi X le_rfl
  simp only [pow_zero, mul_one] at ht hp
  rw [rpow_def_of_pos hX] at ht hp
  have hlog : log X = 300 := by dsimp [X]; rw [log_exp]
  rw [hlog] at ht hp
  norm_num only at ht hp
  have hnum : |(primeCounting X - Li X) / (X / 300) -
      (Chebyshev.theta X - X) / X| ≤ (0.02634 : ℝ) * exp (-(75 / 2 : ℝ)) := by
    have htri : |(primeCounting X - Li X) / (X / 300) -
        (Chebyshev.theta X - X) / X| ≤
          |(primeCounting X - Li X) / (X / 300)| + |(Chebyshev.theta X - X) / X| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le ((primeCounting X - Li X) / (X / 300))
          (-((Chebyshev.theta X - X) / X)))
    simp only [abs_div, abs_of_pos hX,
      abs_of_pos (by norm_num : (0 : ℝ) < 300)] at htri
    unfold Eπ at hp
    unfold Eθ at ht
    rw [hlog] at hp
    linarith
  have hcut : 2 * sqrt (300 : ℝ) - 300 / 8 ≤ -2 := by
    nlinarith [sq_nonneg (sqrt (300 : ℝ) - 16),
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 300)]
  have hratio : exp (2 * sqrt (300 : ℝ) - 300 / 8) ≤ (10 / 27 : ℝ) ^ 2 :=
    (exp_le_exp.mpr hcut).trans (QRHPropagation.exp_neg_nat_upper 2)
  have hexp : exp (-(75 / 2 : ℝ)) ≤
      (10 / 27 : ℝ) ^ 2 * exp (-2 * sqrt (300 : ℝ)) := by
    have hsplit : exp (-(75 / 2 : ℝ)) =
        exp (-2 * sqrt (300 : ℝ)) * exp (2 * sqrt (300 : ℝ) - 300 / 8) := by
      rw [← exp_add]; congr 1; ring
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left hratio (exp_pos (-2 * sqrt (300 : ℝ))).le
    nlinarith
  have hanchor : |(primeCounting X - Li X) / (X / 300) -
      (Chebyshev.theta X - X) / X| / d ≤ 0.41 := by
    apply (div_le_iff₀ hd).mpr
    have hn : (0.02634 : ℝ) * (10 / 27 : ℝ) ^ 2 ≤ 0.41 * (0.0000001 * 300 ^ 2) := by
      norm_num
    have h := mul_le_mul_of_nonneg_right hn (exp_pos (-2 * sqrt (300 : ℝ))).le
    have h' := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 0.02634)
    dsimp [d]
    nlinarith
  have hD := dawson_le_one (show 3 ≤ sqrt (300 : ℝ) - 1 by linarith)
  have hDterm : 2 * dawson (sqrt (300 : ℝ) - 1) / sqrt (300 : ℝ) ≤ 0.12 := by
    apply (div_le_iff₀ (by positivity : 0 < sqrt (300 : ℝ))).mpr
    linarith
  rw [heq]
  linarith

theorem psi_classical_300 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasClassicalBound Eψ 0.00000003 2 2 1 (exp 300) := by
  apply classical_of_logfree (C := 0.01310) (by norm_num) (by norm_num) (by norm_num)
  intro x hx
  convert hpsi 300 0.01310 (by norm_num [CH2.v6.densityFrontier]) x hx using 1 <;> norm_num

theorem theta_classical_300 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasClassicalBound Eθ 0.00000003 2 2 1 (exp 300) := by
  exact classical_of_logfree (by norm_num) (by norm_num) (by norm_num) (theta_300 hpsi)

theorem pi_classical_300 (hpsi : QRHCH2.v2.psi_density_frontier) :
    HasClassicalBound Eπ 0.00000003 2 2 1 (exp 300) := by
  exact classical_of_logfree (by norm_num) (by norm_num) (by norm_num) (pi_density_300 hpsi)

theorem fks_pi_from_correction
    (hθ : HasClassicalBound Eθ 0.00000003 2 2 1 (exp 300))
    (hmu : muAsymp 0.0000001 2 2 1 (exp 300) (exp 300) ≤ 0.6)
    (h3 : FKS2.v2.theorem_3) :
    HasClassicalBound Eπ 0.00000016 2 2 1 (exp 300) := by
  have ht : HasClassicalBound Eθ 0.0000001 2 2 1 (exp 300) := by
    intro x hx
    apply (hθ x hx).trans
    unfold admissibleBound
    norm_num only [rpow_two, div_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num)
        (sq_nonneg (log x))) (by positivity)
  have hp : HasClassicalBound Eπ
      ((1 + muAsymp 0.0000001 2 2 1 (exp 300) (exp 300)) * 0.0000001)
      2 2 1 (exp 300) := by
    apply h3 0.0000001 2 2 1 (exp 300) (exp 300)
    · norm_num
    · norm_num
    · linarith [add_one_le_exp (300 : ℝ)]
    · norm_num
    · norm_num
    · rw [log_exp]; norm_num
    · norm_num
    · exact ht
  intro x hx
  apply (hp x hx).trans
  unfold admissibleBound
  norm_num only [rpow_two, div_one]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg (log x))
  linarith

/-- A common comparison covers all old FKS/FKS2 registered classical shapes. -/
theorem classical_envelope_strict {A B C R x : ℝ} (hA : 1 / 10000 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 1 ≤ R) (hR300 : R ≤ 300)
    (hCR : C ^ 2 ≤ R) (hx : exp 300 ≤ x) :
    admissibleBound 0.00000003 2 2 1 x < admissibleBound A B C R x := by
  have hx0 : 0 < x := (exp_pos (300 : ℝ)).trans_le hx
  let L := log x
  have hL : 300 ≤ L := by
    have h := log_le_log (exp_pos (300 : ℝ)) hx
    simpa [L] using h
  have hL0 : 0 ≤ L := by linarith
  have hR0 : 0 < R := by linarith
  have hLR1 : 1 ≤ L / R := (le_div_iff₀ hR0).mpr (by linarith)
  have hLR0 : 0 ≤ L / R := by positivity
  have hpow : 1 ≤ (L / R) ^ B := one_le_rpow hLR1 hB
  have hrootSq : (C * sqrt (L / R)) ^ 2 ≤ L := by
    calc
      _ = C ^ 2 * (L / R) := by rw [mul_pow, sq_sqrt hLR0]
      _ ≤ R * (L / R) := mul_le_mul_of_nonneg_right hCR hLR0
      _ = L := by field_simp
  have hroot : C * sqrt (L / R) ≤ sqrt L := by
    have hp : 0 ≤ C * sqrt (L / R) := by positivity
    nlinarith [sq_sqrt hL0, sqrt_nonneg L]
  have hex : exp (-sqrt L) ≤ exp (-C * sqrt (L / R)) :=
    exp_le_exp.mpr (by linarith)
  have hs4 : 4 ≤ sqrt L := by nlinarith [sq_sqrt hL0, sqrt_nonneg L]
  have hdec := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 4
    (L0 := (4 : ℝ)) (c := (1 : ℝ)) (by norm_num) (by norm_num) hs4
  have hfour : (sqrt L) ^ 4 = L ^ 2 := by
    rw [show (sqrt L) ^ 4 = ((sqrt L) ^ 2) ^ 2 from by ring, sq_sqrt hL0]
  rw [hfour] at hdec
  norm_num at hdec
  have he4 : exp (-(4 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  have hpoly : L ^ 2 * exp (-sqrt L) ≤ 256 := by linarith
  have hsmall : (0.00000003 : ℝ) * L ^ 2 * exp (-sqrt L) < A := by
    nlinarith
  have hsplit : exp (-2 * sqrt L) = exp (-sqrt L) * exp (-sqrt L) := by
    rw [← exp_add]; congr 1; ring
  have hnew : (0.00000003 : ℝ) * L ^ 2 * exp (-2 * sqrt L) < A * exp (-sqrt L) := by
    rw [hsplit]
    nlinarith [mul_lt_mul_of_pos_right hsmall (exp_pos (-sqrt L))]
  have ha0 : 0 ≤ A := by linarith
  have hAprod := mul_le_mul_of_nonneg_left hpow ha0
  have hold : A * exp (-sqrt L) ≤ A * (L / R) ^ B * exp (-C * sqrt (L / R)) := by
    have hm := mul_le_mul hAprod hex (exp_pos (-sqrt L)).le (by positivity)
    simpa only [mul_one] using hm
  have hfinal := hnew.trans_le hold
  simpa only [admissibleBound, div_one, rpow_two, ← sqrt_eq_rpow, neg_mul, L] using hfinal

/-- Preserve the old small-x claim and improve only where the new ray is established. -/
theorem hybrid_classical {E : ℝ → ℝ} {A B C R X₀ : ℝ}
    (hOld : HasClassicalBound E A B C R X₀)
    (hNew : HasClassicalBound E 0.00000003 2 2 1 (exp 300)) :
    ∀ x ≥ X₀, E x ≤ if exp 300 ≤ x then
      min (admissibleBound A B C R x) (admissibleBound 0.00000003 2 2 1 x)
      else admissibleBound A B C R x := by
  intro x hx
  by_cases ht : exp 300 ≤ x
  · rw [if_pos ht]
    exact le_min (hOld x hx) (hNew x ht)
  · rw [if_neg ht]
    exact hOld x hx

end QRHPhase2
