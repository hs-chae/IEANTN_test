/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityLogTail

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

theorem power_log_tail_nonpos {p q H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hp : 0 ≤ p) (hq : q ≤ 0) (hp1 : p < 1) :
    T ^ p * Real.log T ^ q / T +
      (∫ u in H..T, u ^ p * Real.log u ^ q / u ^ 2) ≤
      H ^ (p - 1) * Real.log H ^ q / (1 - p) := by
  set d := 1 - p with hddef
  have hH0 : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hT1 : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  set A : ℝ → ℝ := fun u ↦ u ^ (p - 1) * Real.log u ^ q
  set f : ℝ → ℝ := fun u ↦ u ^ p * Real.log u ^ q / u ^ 2
  have hAder : ∀ u : ℝ, 1 < u → HasDerivAt A
      (u ^ (p - 2) * Real.log u ^ q * (p - 1 + q / Real.log u)) u := by
    intro u hu
    exact hasDerivAt_power_log_tail hu
  have hgcont : ContinuousOn (fun u ↦ - A u / d) (Icc H T) := by
    intro u hu
    exact (((hAder u (hH.trans_le hu.1)).neg).div_const d).continuousAt.continuousWithinAt
  have hfcont : ContinuousOn f (Icc H T) := by
    intro u hu
    have hu1 : 1 < u := hH.trans_le hu.1
    have hu0 : 0 < u := by linarith
    have hlu : 0 < Real.log u := Real.log_pos hu1
    exact ((((Real.continuousAt_rpow_const u p (Or.inl hu0.ne')).mul
      ((Real.continuousAt_log hu0.ne').rpow_const (p := q) (Or.inl hlu.ne'))).div
      ((continuousAt_id.pow 2)) (pow_ne_zero 2 hu0.ne'))).continuousWithinAt
  have hint : IntegrableOn f (Icc H T) := hfcont.integrableOn_Icc
  have hgder : ∀ u ∈ Ioo H T,
      HasDerivWithinAt (fun v ↦ - A v / d)
      (-(u ^ (p - 2) * Real.log u ^ q * (p - 1 + q / Real.log u)) / d) (Ioi u) u := by
    intro u hu
    exact (((hAder u (hH.trans hu.1)).neg).div_const d).hasDerivWithinAt
  have hcmp : ∀ u ∈ Ioo H T, f u ≤
      -(u ^ (p - 2) * Real.log u ^ q * (p - 1 + q / Real.log u)) / d := by
    intro u hu
    have hu1 : 1 < u := hH.trans hu.1
    have hu0 : 0 < u := by linarith
    have hlogu : 0 < Real.log u := Real.log_pos hu1
    have hratio : q / Real.log u ≤ 0 := div_nonpos_of_nonpos_of_nonneg hq hlogu.le
    have hf0 : 0 ≤ f u := by dsimp [f]; positivity
    have heq : u ^ (p - 2) * Real.log u ^ q = f u := by
      dsimp [f]
      rw [Real.rpow_sub hu0, Real.rpow_two]
      ring
    rw [heq, le_div_iff₀ hd0]
    have hcoef : p - 1 + q / Real.log u ≤ -d := by dsimp [d]; linarith
    have hh := mul_le_mul_of_nonneg_left hcoef hf0
    nlinarith
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hHT hgcont hgder hint hcmp
  have hie : (∫ u in H..T, f u) * d ≤ A H - A T := by
    have hh := mul_le_mul_of_nonneg_right hi hd0.le
    field_simp at hh
    nlinarith
  have hAT0 : 0 ≤ A T := by
    exact mul_nonneg (Real.rpow_pos_of_pos hT0 (p - 1)).le
      (Real.rpow_pos_of_pos (Real.log_pos hT1) q).le
  have hfirst : T ^ p * Real.log T ^ q / T = A T := by
    dsimp [A]
    rw [Real.rpow_sub hT0, Real.rpow_one]
    ring
  rw [hfirst]
  change A T + (∫ u in H..T, f u) ≤ A H / d
  apply (le_div_iff₀ hd0).mpr
  have hh := mul_le_mul_of_nonneg_left hd1 hAT0
  nlinarith

/-- The derivative identity used in finite height integration by parts. -/
theorem hasDerivAt_power_log_moment {p q u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun v : ℝ ↦ v ^ (p - 1) * Real.log v ^ q)
      (-(1 - p) * (u ^ p * Real.log u ^ q / u ^ 2) +
        q * (u ^ p * Real.log u ^ (q - 1) / u ^ 2)) u := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  convert hasDerivAt_power_log_tail (p := p) (q := q) hu using 1
  rw [Real.rpow_sub hu0, Real.rpow_two, Real.rpow_sub_one hlu.ne' q]
  ring

/-- One integration-by-parts step, keeping the finite upper-height boundary. -/
theorem power_log_tail_step {p q H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hp : 0 ≤ p) (hp1 : p < 1) (hq : 0 ≤ q) :
    T ^ p * Real.log T ^ q / T +
      (∫ u in H..T, u ^ p * Real.log u ^ q / u ^ 2) ≤
      H ^ (p - 1) * Real.log H ^ q / (1 - p) + q / (1 - p) *
        (T ^ p * Real.log T ^ (q - 1) / T +
          ∫ u in H..T, u ^ p * Real.log u ^ (q - 1) / u ^ 2) := by
  have hr : 0 < 1 - p := by linarith
  have hT1 : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hI := power_log_intervalIntegrable (p := p) (q := q) hH hHT
  have hJ := power_log_intervalIntegrable (p := p) (q := q - 1) hH hHT
  have hder : ∀ u ∈ Set.uIcc H T,
      HasDerivAt (fun v : ℝ ↦ v ^ (p - 1) * Real.log v ^ q)
        (-(1 - p) * (u ^ p * Real.log u ^ q / u ^ 2) +
          q * (u ^ p * Real.log u ^ (q - 1) / u ^ 2)) u := by
    intro u hu
    rw [Set.uIcc_of_le hHT] at hu
    exact hasDerivAt_power_log_moment (hH.trans_le hu.1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((hI.const_mul (-(1 - p))).add (hJ.const_mul q))
  rw [intervalIntegral.integral_add (hI.const_mul (-(1 - p))) (hJ.const_mul q),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  have hAT : T ^ (p - 1) * Real.log T ^ q = T ^ p * Real.log T ^ q / T := by
    rw [Real.rpow_sub hT0, Real.rpow_one]; ring
  rw [hAT] at he
  have hlT : 0 < Real.log T := Real.log_pos hT1
  have hA0 : 0 ≤ T ^ p * Real.log T ^ q / T := by positivity
  have hB0 : 0 ≤ T ^ p * Real.log T ^ (q - 1) / T := by positivity
  rw [div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ hr).mpr
  nlinarith [mul_nonneg hp hA0, mul_nonneg hq hB0]

/-- The four-step density-tail envelope; the next integration-by-parts remainder is nonpositive. -/
theorem power_log_tail_four {p q H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hp : 0 ≤ p) (hp1 : p < 1) (hq : 3 ≤ q) (hq4 : q ≤ 4) :
    T ^ p * Real.log T ^ q / T +
      (∫ u in H..T, u ^ p * Real.log u ^ q / u ^ 2) ≤
      H ^ (p - 1) * Real.log H ^ q / (1 - p) *
        (1 + q / ((1 - p) * Real.log H) +
          q * (q - 1) / ((1 - p) * Real.log H) ^ 2 +
          q * (q - 1) * (q - 2) / ((1 - p) * Real.log H) ^ 3 +
          q * (q - 1) * (q - 2) * (q - 3) / ((1 - p) * Real.log H) ^ 4) := by
  have hr : 0 < 1 - p := by linarith
  have hl : 0 < Real.log H := Real.log_pos hH
  let A : ℝ → ℝ := fun z ↦ H ^ (p - 1) * Real.log H ^ z / (1 - p)
  let B : ℝ → ℝ := fun z ↦ T ^ p * Real.log T ^ z / T +
    ∫ u in H..T, u ^ p * Real.log u ^ z / u ^ 2
  have h0 : B (q - 4) ≤ A (q - 4) := power_log_tail_nonpos hH hHT hp (by linarith) hp1
  have hs : ∀ z : ℝ, 0 ≤ z → B z ≤ A z + z / (1 - p) * B (z - 1) := by
    intro z hz; exact power_log_tail_step hH hHT hp hp1 hz
  have h3 := hs (q - 3) (by linarith)
  have h2 := hs (q - 2) (by linarith)
  have h1 := hs (q - 1) (by linarith)
  have h := hs q (by linarith)
  have e3 : q - 3 - 1 = q - 4 := by ring
  have e2 : q - 2 - 1 = q - 3 := by ring
  have e1 : q - 1 - 1 = q - 2 := by ring
  rw [e3] at h3; rw [e2] at h2; rw [e1] at h1
  have he : B q ≤ A q + q / (1 - p) *
      (A (q - 1) + (q - 1) / (1 - p) *
        (A (q - 2) + (q - 2) / (1 - p) *
          (A (q - 3) + (q - 3) / (1 - p) * A (q - 4)))) := by
    have c3 : 0 ≤ (q - 3) / (1 - p) := div_nonneg (by linarith) hr.le
    have c2 : 0 ≤ (q - 2) / (1 - p) := div_nonneg (by linarith) hr.le
    have c1 : 0 ≤ (q - 1) / (1 - p) := div_nonneg (by linarith) hr.le
    have c0 : 0 ≤ q / (1 - p) := div_nonneg (by linarith) hr.le
    exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (h1.trans (add_le_add_right (mul_le_mul_of_nonneg_left
        (h2.trans (add_le_add_right (mul_le_mul_of_nonneg_left
          (h3.trans (add_le_add_right (mul_le_mul_of_nonneg_left h0 c3) _)) c2) _)) c1) _)) c0) _)
  change B q ≤ _
  convert he using 1
  dsimp [A]
  rw [Real.rpow_sub hl, Real.rpow_sub hl, Real.rpow_sub hl, Real.rpow_sub hl]
  rw [Real.rpow_one, Real.rpow_two, show (3 : ℝ) = (3 : ℕ) by norm_num,
    show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  field_simp
  <;> ring

/-- The logarithmic-square term has an exact two-step upper tail. -/
theorem log_square_reciprocal_tail {H T : ℝ} (hH : 1 < H) (hHT : H ≤ T) :
    Real.log T ^ (2 : ℕ) / T + (∫ u in H..T, Real.log u ^ (2 : ℕ) / u ^ 2) ≤
      (Real.log H ^ (2 : ℕ) + 2 * Real.log H + 2) / H := by
  have h0 := power_log_tail_nonpos (p := 0) (q := 0) hH hHT (by norm_num)
    (by norm_num) (by norm_num)
  have h1 := power_log_tail_step (p := 0) (q := 1) hH hHT (by norm_num)
    (by norm_num) (by norm_num)
  have h2 := power_log_tail_step (p := 0) (q := 2) hH hHT (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [Real.rpow_zero, Real.rpow_one, Real.rpow_two] at h0 h1 h2
  have hh : H ^ (-1 : ℝ) = 1 / H := by rw [Real.rpow_neg_one, one_div]
  rw [hh] at h0 h1 h2
  calc
    _ ≤ (1 / H) * Real.log H ^ (2 : ℕ) + 2 * ((1 / H) * Real.log H + 1 / H) := by linarith
    _ = _ := by ring

/-- Four-moment closed form for the first FKS density term. -/
noncomputable def densityMomentMain (σ H : ℝ) : ℝ :=
  let p := 8 * (1 - σ) / 3
  let q := 5 - 2 * σ
  H ^ (p - 1) * Real.log H ^ q / (1 - p) *
    (1 + q / ((1 - p) * Real.log H) +
      q * (q - 1) / ((1 - p) * Real.log H) ^ 2 +
      q * (q - 1) * (q - 2) / ((1 - p) * Real.log H) ^ 3 +
      q * (q - 1) * (q - 2) * (q - 3) / ((1 - p) * Real.log H) ^ 4)

/-- Eliminate the inner height integral with the sharp envelope used by all twelve rows. -/
theorem fks_density_reciprocal_moment_bound {σ H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8) :
    fksDensityMajorant σ T / T + (∫ u in H..T, fksDensityMajorant σ u / u ^ 2) ≤
      9.795 * densityMomentMain σ H +
        4.465 * ((Real.log H ^ (2 : ℕ) + 2 * Real.log H + 2) / H) := by
  have h1 := power_log_tail_four (p := 8 * (1 - σ) / 3) (q := 5 - 2 * σ)
    hH hHT (by linarith) (by linarith) (by linarith) (by linarith)
  have h2 := log_square_reciprocal_tail hH hHT
  have hi1 := power_log_intervalIntegrable (p := 8 * (1 - σ) / 3) (q := 5 - 2 * σ) hH hHT
  have hi2 := power_log_intervalIntegrable (p := 0) (q := 2) hH hHT
  have he : (fun u : ℝ ↦ fksDensityMajorant σ u / u ^ 2) =
      (fun u : ℝ ↦ 9.795 * (u ^ (8 * (1 - σ) / 3) * Real.log u ^ (5 - 2 * σ) / u ^ 2) +
        4.465 * (u ^ (0 : ℝ) * Real.log u ^ (2 : ℝ) / u ^ 2)) := by
    funext u
    simp only [fksDensityMajorant, Real.rpow_zero, Real.rpow_two]
    ring
  rw [he, intervalIntegral.integral_add (hi1.const_mul 9.795) (hi2.const_mul 4.465),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [fksDensityMajorant, Real.rpow_zero, Real.rpow_two] at *
  simp only [one_mul] at *
  calc
    _ = 9.795 * (T ^ (8 * (1 - σ) / 3) * Real.log T ^ (5 - 2 * σ) / T +
        ∫ u in H..T, u ^ (8 * (1 - σ) / 3) * Real.log u ^ (5 - 2 * σ) / u ^ 2) +
      4.465 * (Real.log T ^ (2 : ℕ) / T + ∫ u in H..T, Real.log u ^ (2 : ℕ) / u ^ 2) := by ring
    _ ≤ _ := by dsimp [densityMomentMain]; nlinarith

/-- The finite density weight is bounded by the actual four-moment certificate envelope. -/
theorem finiteDensityWeight_le_moments {σ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    finiteDensityWeight σ t ≤
      2 * (9.795 * densityMomentMain σ (3 * (10 : ℝ) ^ (12 : ℕ)) +
        4.465 * ((Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) ^ (2 : ℕ) +
          2 * Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) + 2) / (3 * (10 : ℝ) ^ (12 : ℕ)))) +
      4 * Real.pi / t * fksDensityMajorant σ t := by
  have hb := fks_density_reciprocal_moment_bound
    (H := 3 * (10 : ℝ) ^ (12 : ℕ)) (by norm_num) ht hσ hσ'
  unfold finiteDensityWeight
  linarith

end CH2QRH
