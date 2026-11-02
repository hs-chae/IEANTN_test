/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RemaindersPhase2
namespace QRHPhase2
open Real IEANTN DudekPlattNumerics.Calculus
open DudekPlattNumerics.v4.Numerics (poly_exp_decreasing exp_neg_nat_le)

theorem theta_point_phase2 (hpsi : QRHCH2.v2.psi_density_frontier)
    {L : ℝ} (hL : 144 ≤ L) :
    L ^ 6 / exp L * |thetaError (exp L) / L| < 33 := by
  have hLpos : 0 < L := by linarith
  have hb := theta_128 hpsi (exp L) (exp_le_exp.mpr (by linarith))
  simp only [pow_zero, mul_one, rpow_def_of_pos (exp_pos L), log_exp] at hb
  have hs : L ^ 5 * Eθ (exp L) ≤ (0.03014 : ℝ) * L ^ 5 * exp (-L / 8) := by
    rw [show L * ((7 / 8 : ℝ) - 1) = -L / 8 by ring] at hb
    calc
      _ ≤ L ^ 5 * (0.03014 * exp (-L / 8)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hd := poly_exp_decreasing 5 (L0 := (144 : ℝ)) (c := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hd' : L ^ 5 * exp (-L / 8) ≤ (144 : ℝ) ^ 5 * exp (-18) := by
    convert hd using 1 <;> congr 1 <;> ring
  have hep := QRHPropagation.exp_neg_nat_upper 18
  have hf : (0.03014 : ℝ) * L ^ 5 * exp (-L / 8) < 33 := by
    calc
      _ ≤ 0.03014 * ((144 : ℝ) ^ 5 * exp (-18)) := by linarith
      _ ≤ 0.03014 * ((144 : ℝ) ^ 5 * (10 / 27 : ℝ) ^ 18) := by gcongr; simpa using hep
      _ < _ := by norm_num
  have hid : L ^ 6 / exp L * |thetaError (exp L) / L| = L ^ 5 * Eθ (exp L) := by
    rw [abs_div, abs_of_pos hLpos]
    dsimp [Eθ, thetaError]
    field_simp
  rw [hid]
  exact hs.trans_lt hf

theorem integral_phase2 (hpsi : QRHCH2.v2.psi_density_frontier)
    {L : ℝ} (hL : 144 ≤ L) :
    L ^ 6 / exp L * |errorIntegral (exp L)| < 3 := by
  have hLpos : 0 < L := by linarith
  have hs : 2 ≤ exp (3 * L / 4) := by linarith [add_one_le_exp (3 * L / 4)]
  have hsx : exp (3 * L / 4) ≤ exp L := exp_le_exp.mpr (by linarith)
  have htail : HasPowerLogBound Eθ (((16 / 9 : ℝ) * 0.08350) / L ^ 2)
      2 (7 / 8) (exp (3 * L / 4)) := by
    intro t ht
    have ht0 : 0 < t := (exp_pos (3 * L / 4)).trans_le ht
    have hlog : 3 * L / 4 ≤ log t := by
      have hh := log_le_log (exp_pos (3 * L / 4)) ht
      simpa only [log_exp] using hh
    have hlogs : (3 * L / 4) ^ 2 ≤ log t ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlog 2
    have hcoef : (0.08350 : ℝ) ≤
        (((16 / 9 : ℝ) * 0.08350) / L ^ 2) * log t ^ 2 := by
      rw [show (((16 / 9 : ℝ) * 0.08350) / L ^ 2) * log t ^ 2 =
        (((16 / 9 : ℝ) * 0.08350) * log t ^ 2) / L ^ 2 from by ring]
      apply (le_div_iff₀ (pow_pos hLpos 2)).mpr
      nlinarith
    have hpoint := theta_96 hpsi t
      ((exp_le_exp.mpr (by linarith : (96 : ℝ) ≤ 3 * L / 4)).trans ht)
    simp only [pow_zero, mul_one] at hpoint
    exact hpoint.trans (mul_le_mul_of_nonneg_right hcoef (rpow_pos_of_pos ht0 _).le)
  have hi := QRHPiPower.error_integral_bound
    (A := (((16 / 9 : ℝ) * 0.08350) / L ^ 2)) (β := (7 / 8 : ℝ))
    (by positivity) (by norm_num) hs hsx htail
  rw [rpow_def_of_pos (exp_pos L), log_exp] at hi
  have hseven : exp (L * (7 / 8 : ℝ)) = exp (7 * L / 8) := by congr 1; ring
  rw [hseven] at hi
  have hn : L ^ 6 / exp L * |errorIntegral (exp L)| ≤
      4 * L ^ 6 * exp (-L / 4) + (128 * 0.08350 / 63 : ℝ) * L ^ 4 * exp (-L / 8) := by
    calc
      _ ≤ L ^ 6 / exp L * (4 * exp (3 * L / 4) +
        (((16 / 9 : ℝ) * 0.08350) / L ^ 2) / (7 / 8) * exp (7 * L / 8)) := by gcongr
      _ = _ := by
        rw [show 3 * L / 4 = L + (-L / 4) by ring,
          show 7 * L / 8 = L + (-L / 8) by ring, exp_add, exp_add]
        field_simp
        ring
  have hd1 := poly_exp_decreasing 6 (L0 := (144 : ℝ)) (c := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) hL
  have hd2 := poly_exp_decreasing 4 (L0 := (144 : ℝ)) (c := (1 / 8 : ℝ))
    (by norm_num) (by norm_num) hL
  have hh1 : L ^ 6 * exp (-L / 4) ≤ (144 : ℝ) ^ 6 * exp (-36) := by
    convert hd1 using 1 <;> congr 1 <;> ring
  have hh2 : L ^ 4 * exp (-L / 8) ≤ (144 : ℝ) ^ 4 * exp (-18) := by
    convert hd2 using 1 <;> congr 1 <;> ring
  calc
    _ ≤ 4 * L ^ 6 * exp (-L / 4) +
        (128 * 0.08350 / 63 : ℝ) * L ^ 4 * exp (-L / 8) := hn
    _ ≤ 4 * ((144 : ℝ) ^ 6 * exp (-36)) +
        (128 * 0.08350 / 63 : ℝ) * ((144 : ℝ) ^ 4 * exp (-18)) := by linarith
    _ ≤ 4 * ((144 : ℝ) ^ 6 * (10 / 27 : ℝ) ^ 36) +
        (128 * 0.08350 / 63 : ℝ) * ((144 : ℝ) ^ 4 * (10 / 27 : ℝ) ^ 18) := by
      gcongr <;> exact QRHPropagation.exp_neg_nat_upper _
    _ < _ := by norm_num

theorem pi_coefficients_phase2 (hpsi : QRHCH2.v2.psi_density_frontier)
    {L : ℝ} (hL : 144 ≤ L) :
    70 < L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) ∧
      L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) < 170 := by
  have hLpos : 0 < L := by linarith
  have hL0 := hLpos.ne'
  have he0 := (exp_pos L).ne'
  have hx : 2 ≤ exp L := by linarith [add_one_le_exp L]
  have hq : 0 < L ^ 6 / exp L := by positivity
  have hp : |L ^ 6 / exp L * (thetaError (exp L) / L)| < 33 := by
    rw [abs_mul, abs_of_pos hq]
    exact theta_point_phase2 hpsi hL
  have he : |L ^ 6 / exp L * errorIntegral (exp L)| < 3 := by
    rw [abs_mul, abs_of_pos hq]
    exact integral_phase2 hpsi hL
  have hi : L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) < 13 :=
    normalized_I7_phase2 hL
  have hi0 : 0 ≤ L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) := by
    exact mul_nonneg hq.le (mul_nonneg (by norm_num) (logIntegral_nonneg 7 hx))
  have ha : L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) < 1 := by
    convert scalar_A_phase2 hL using 1
    rw [exp_neg]
    ring
  have ha0 : 0 ≤ L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) := by
    have : 0 ≤ DudekPlattNumerics.Calculus.A := by
      unfold DudekPlattNumerics.Calculus.A
      have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
      positivity
    positivity
  have hn : L ^ 6 / exp L * (primeCounting (exp L) - S5 (exp L)) =
      120 + L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) -
        L ^ 6 / exp L * (2 * DudekPlattNumerics.Calculus.A) +
        L ^ 6 / exp L * (thetaError (exp L) / L) +
        L ^ 6 / exp L * errorIntegral (exp L) := by
    rw [primeCounting_expansion hx, log_exp]
    field_simp
    ring
  rw [hn]
  rcases abs_lt.mp hp with ⟨hp1, hp2⟩
  rcases abs_lt.mp he with ⟨he1, he2⟩
  constructor <;> linarith

theorem pi_expansion_phase2 (hpsi : QRHCH2.v2.psi_density_frontier)
    {x : ℝ} (hx : exp 144 < x) :
    DudekPlatt.v3.mainTerm x + 70 * x / log x ^ 6 < primeCounting x ∧
      primeCounting x < DudekPlatt.v3.mainTerm x + 170 * x / log x ^ 6 := by
  have hx0 : 0 < x := (exp_pos (144 : ℝ)).trans hx
  have hL : 144 ≤ log x := by
    have h := log_lt_log (exp_pos (144 : ℝ)) hx
    simpa using h.le
  have hl : 0 < log x := by linarith
  have hq : 0 < log x ^ 6 / x := by positivity
  have hcoef := pi_coefficients_phase2 hpsi hL
  rw [exp_log hx0] at hcoef
  have hinv : (log x ^ 6 / x) * (x / log x ^ 6) = 1 := by field_simp
  change S5 x + 70 * x / log x ^ 6 < primeCounting x ∧
    primeCounting x < S5 x + 170 * x / log x ^ 6
  have h1 : 70 / (log x ^ 6 / x) < primeCounting x - S5 x :=
    (div_lt_iff₀ hq).mpr (by simpa [mul_comm] using hcoef.1)
  have h2 : primeCounting x - S5 x < 170 / (log x ^ 6 / x) :=
    (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using hcoef.2)
  have hid (c : ℝ) : c / (log x ^ 6 / x) = c * x / log x ^ 6 := by
    field_simp
  rw [hid] at h1 h2
  constructor <;> linarith

theorem ramanujan_phase2 (hpsi : QRHCH2.v2.psi_density_frontier)
    (hDP : DudekPlatt.v3.criterion) :
    ∀ x : ℝ, exp 145 < x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  apply hDP 70 170 (exp 144) (exp 145)
  · linarith [add_one_le_exp (144 : ℝ)]
  · intro x hx
    exact (pi_expansion_phase2 hpsi hx).1
  · intro x hx
    have heq : exp 1 * exp 144 = exp (145 : ℝ) := by rw [← exp_add]; norm_num
    rw [heq] at hx
    exact (pi_expansion_phase2 hpsi ((exp_le_exp.mpr (by norm_num : (144 : ℝ) ≤ 145)).trans_lt hx)).2
  · rw [← exp_add]; norm_num
  · intro x hx
    have hl : 144 ≤ log x := by
      have h := log_lt_log (exp_pos (145 : ℝ)) hx
      rw [log_exp] at h
      linarith
    have hl0 : 0 < log x := by linarith
    have h1 : (472 : ℝ) / log x ≤ 472 / 144 := by gcongr
    have h2 : (968 : ℝ) / log x ^ 2 ≤ 968 / 144 ^ 2 := by gcongr
    have h3 : (2616 : ℝ) / log x ^ 3 ≤ 2616 / 144 ^ 3 := by gcongr
    have h4 : (8160 : ℝ) / log x ^ 4 ≤ 8160 / 144 ^ 4 := by gcongr
    have h5 : (28900 : ℝ) / log x ^ 5 ≤ 28900 / 144 ^ 5 := by gcongr
    have hup : DudekPlatt.v3.εUpper 170 x < 416 := by
      unfold DudekPlatt.v3.εUpper
      norm_num at h1 h2 h3 h4 h5 ⊢
      linarith
    have hpos : 0 ≤ 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 +
        97 / log x ^ 4 + 30 / log x ^ 5 + 8 / log x ^ 6 := by positivity
    have hlo : 276 ≤ DudekPlatt.v3.εLower 70 (exp 144) x := by
      norm_num [DudekPlatt.v3.εLower, DudekPlatt.v3.εPos]
      linarith
    linarith
theorem ramanujan_of_expansion
    (hπ : ∀ x : ℝ, exp 144 < x →
      DudekPlatt.v3.mainTerm x + 70 * x / log x ^ 6 < primeCounting x ∧
      primeCounting x < DudekPlatt.v3.mainTerm x + 170 * x / log x ^ 6)
    (hDP : DudekPlatt.v3.criterion) :
    ∀ x : ℝ, exp 145 < x →
      primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1) := by
  apply hDP 70 170 (exp 144) (exp 145)
  · linarith [add_one_le_exp (144 : ℝ)]
  · intro x hx
    exact (hπ x hx).1
  · intro x hx
    have heq : exp 1 * exp 144 = exp (145 : ℝ) := by rw [← exp_add]; norm_num
    rw [heq] at hx
    exact (hπ x ((exp_le_exp.mpr (by norm_num : (144 : ℝ) ≤ 145)).trans_lt hx)).2
  · rw [← exp_add]; norm_num
  · intro x hx
    have hl : 144 ≤ log x := by
      have h := log_lt_log (exp_pos (145 : ℝ)) hx
      rw [log_exp] at h
      linarith
    have hl0 : 0 < log x := by linarith
    have h1 : (472 : ℝ) / log x ≤ 472 / 144 := by gcongr
    have h2 : (968 : ℝ) / log x ^ 2 ≤ 968 / 144 ^ 2 := by gcongr
    have h3 : (2616 : ℝ) / log x ^ 3 ≤ 2616 / 144 ^ 3 := by gcongr
    have h4 : (8160 : ℝ) / log x ^ 4 ≤ 8160 / 144 ^ 4 := by gcongr
    have h5 : (28900 : ℝ) / log x ^ 5 ≤ 28900 / 144 ^ 5 := by gcongr
    have hup : DudekPlatt.v3.εUpper 170 x < 416 := by
      unfold DudekPlatt.v3.εUpper
      norm_num at h1 h2 h3 h4 h5 ⊢
      linarith
    have hpos : 0 ≤ 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 +
        97 / log x ^ 4 + 30 / log x ^ 5 + 8 / log x ^ 6 := by positivity
    have hlo : 276 ≤ DudekPlatt.v3.εLower 70 (exp 144) x := by
      norm_num [DudekPlatt.v3.εLower, DudekPlatt.v3.εPos]
      linarith
    linarith
end QRHPhase2
