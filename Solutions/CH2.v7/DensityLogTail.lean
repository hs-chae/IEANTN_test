/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityTail

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- Differentiating the power-log density-tail primitive. -/
theorem hasDerivAt_power_log_tail {p q u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun v : ℝ ↦ v ^ (p - 1) * (Real.log v) ^ q)
      (u ^ (p - 2) * Real.log u ^ q * (p - 1 + q / Real.log u)) u := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  have h1 := Real.hasDerivAt_rpow_const (x := u) (p := p - 1) (Or.inl hu0.ne')
  have h2 := (Real.hasDerivAt_log hu0.ne').rpow_const (p := q) (Or.inl hlu.ne')
  have hp : u ^ (p - 1) = u ^ (p - 2) * u := by
    calc u ^ (p - 1) = u ^ ((p - 2) + 1) := by congr 1; ring
      _ = u ^ (p - 2) * u := by rw [Real.rpow_add hu0, Real.rpow_one]
  have hl : Real.log u ^ (q - 1) = Real.log u ^ q / Real.log u :=
    Real.rpow_sub_one hlu.ne' q
  have he : p - 1 - 1 = p - 2 := by ring
  rw [he] at h1
  convert h1.mul h2 using 1 <;> first | rfl | (rw [hp, hl]; field_simp)

/-- A finite-interval density-tail estimate; no improper integral or numerical oracle is used. -/
theorem power_log_reciprocal_tail {p q H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 < 1 - p - q / Real.log H) :
    T ^ p * Real.log T ^ q / T +
      (∫ u in H..T, u ^ p * Real.log u ^ q / u ^ 2) ≤
      H ^ (p - 1) * Real.log H ^ q / (1 - p - q / Real.log H) := by
  set d := 1 - p - q / Real.log H with hddef
  have hH0 : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hT1 : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := hd
  have hd1 : d ≤ 1 := by dsimp [d]; have := div_nonneg hq hlogH.le; linarith
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
    have hratio : q / Real.log u ≤ q / Real.log H :=
      div_le_div_of_nonneg_left hq hlogH (Real.log_le_log hH0 hu.1.le)
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

/-- The power-log reciprocal integrand is integrable on each admissible finite interval. -/
theorem power_log_intervalIntegrable {p q H T : ℝ} (hH : 1 < H) (hHT : H ≤ T) :
    IntervalIntegrable (fun u : ℝ ↦ u ^ p * Real.log u ^ q / u ^ 2) volume H T := by
  have hc : ContinuousOn (fun u : ℝ ↦ u ^ p * Real.log u ^ q / u ^ 2) (Icc H T) := by
    intro u hu
    have hu1 : 1 < u := hH.trans_le hu.1
    have hu0 : 0 < u := by linarith
    have hlu : 0 < Real.log u := Real.log_pos hu1
    exact ((((Real.continuousAt_rpow_const u p (Or.inl hu0.ne')).mul
      ((Real.continuousAt_log hu0.ne').rpow_const (p := q) (Or.inl hlu.ne'))).div
      ((continuousAt_id.pow 2)) (pow_ne_zero 2 hu0.ne'))).continuousWithinAt
  exact hc.intervalIntegrable_of_Icc hHT

/-- Eliminate the inner height integral of the actual FKS majorant using a closed expression. -/
theorem fks_density_reciprocal_closed_bound {σ H T : ℝ} (hH : 1 < H) (hHT : H ≤ T)
    (hp : 0 ≤ 8 * (1 - σ) / 3) (hq : 0 ≤ 5 - 2 * σ)
    (hd : 0 < 1 - 8 * (1 - σ) / 3 - (5 - 2 * σ) / Real.log H)
    (hd2 : 0 < 1 - 2 / Real.log H) :
    fksDensityMajorant σ T / T + (∫ u in H..T, fksDensityMajorant σ u / u ^ 2) ≤
      9.795 * (H ^ (8 * (1 - σ) / 3 - 1) * Real.log H ^ (5 - 2 * σ) /
        (1 - 8 * (1 - σ) / 3 - (5 - 2 * σ) / Real.log H)) +
      4.465 * (H ^ (-1 : ℝ) * Real.log H ^ (2 : ℝ) / (1 - 2 / Real.log H)) := by
  have h1 := power_log_reciprocal_tail hH hHT hp hq hd
  have h2 := power_log_reciprocal_tail (p := 0) (q := 2) hH hHT (by norm_num) (by norm_num)
    (by simpa using hd2)
  have hi1 := power_log_intervalIntegrable (p := 8 * (1 - σ) / 3) (q := 5 - 2 * σ) hH hHT
  have hi2 := power_log_intervalIntegrable (p := 0) (q := 2) hH hHT
  have heq : fksDensityMajorant σ T / T + (∫ u in H..T, fksDensityMajorant σ u / u ^ 2) =
      9.795 * (T ^ (8 * (1 - σ) / 3) * Real.log T ^ (5 - 2 * σ) / T +
        ∫ u in H..T, u ^ (8 * (1 - σ) / 3) * Real.log u ^ (5 - 2 * σ) / u ^ 2) +
      4.465 * (T ^ (0 : ℝ) * Real.log T ^ (2 : ℝ) / T +
        ∫ u in H..T, u ^ (0 : ℝ) * Real.log u ^ (2 : ℝ) / u ^ 2) := by
    have he : (fun u : ℝ ↦ fksDensityMajorant σ u / u ^ 2) =
        (fun u : ℝ ↦ 9.795 * (u ^ (8 * (1 - σ) / 3) * Real.log u ^ (5 - 2 * σ) / u ^ 2) +
          4.465 * (u ^ (0 : ℝ) * Real.log u ^ (2 : ℝ) / u ^ 2)) := by
      funext u
      simp only [fksDensityMajorant, Real.rpow_zero, Real.rpow_two]
      ring
    rw [he, intervalIntegral.integral_add (hi1.const_mul 9.795) (hi2.const_mul 4.465),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp only [fksDensityMajorant, Real.rpow_zero, Real.rpow_two]
    ring
  rw [heq]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 9.795)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4.465)
  simpa only [sub_zero, zero_sub] using add_le_add hh1 hh2

/-- A rationally certified logarithmic lower bound at the verified RH height. -/
theorem log_verified_height_ge_twenty_eight :
    28 ≤ Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) := by
  have hh := (CH2Section7A.exp_nat_bounds 28).2
  have he : Real.exp 28 ≤ 3 * (10 : ℝ) ^ (12 : ℕ) := by
    norm_num at hh ⊢
    linarith
  have hl := Real.log_le_log (Real.exp_pos (28 : ℝ)) he
  simpa using hl

/-- The denominators of the closed FKS tail bound stay positive on the actual sigma interval. -/
theorem density_tail_denominators_pos {σ : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8) :
    0 < 1 - 8 * (1 - σ) / 3 - (5 - 2 * σ) / Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) ∧
      0 < 1 - 2 / Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) := by
  have hl := log_verified_height_ge_twenty_eight
  have hl0 : 0 < Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) := by linarith
  have hq : (5 - 2 * σ) / Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) ≤ 1 / 8 := by
    apply (div_le_iff₀ hl0).mpr
    norm_num at *
    linarith
  have hq2 : (2 : ℝ) / Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) ≤ 1 / 14 := by
    apply (div_le_iff₀ hl0).mpr
    norm_num at *
    linarith
  constructor <;> linarith

/-- Closed height-tail envelope at the verified RH cutoff. -/
noncomputable def densityTailClosed (σ : ℝ) : ℝ :=
  let H : ℝ := 3 * 10 ^ (12 : ℕ)
  9.795 * (H ^ (8 * (1 - σ) / 3 - 1) * Real.log H ^ (5 - 2 * σ) /
    (1 - 8 * (1 - σ) / 3 - (5 - 2 * σ) / Real.log H)) +
  4.465 * (H ^ (-1 : ℝ) * Real.log H ^ (2 : ℝ) / (1 - 2 / Real.log H))

/-- The actual density weight has no remaining inner height integral in this upper bound. -/
theorem finiteDensityWeight_le_closed {σ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (ht : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ t) :
    finiteDensityWeight σ t ≤ 2 * densityTailClosed σ +
      4 * Real.pi / t * fksDensityMajorant σ t := by
  obtain ⟨hd, hd2⟩ := density_tail_denominators_pos hσ hσ'
  have hb := fks_density_reciprocal_closed_bound (H := 3 * (10 : ℝ) ^ (12 : ℕ))
    (by norm_num) ht (by linarith : 0 ≤ 8 * (1 - σ) / 3)
    (by linarith : 0 ≤ 5 - 2 * σ) hd hd2
  change fksDensityMajorant σ t / t +
    (∫ u in (3 * (10 : ℝ) ^ (12 : ℕ))..t, fksDensityMajorant σ u / u ^ 2) ≤ densityTailClosed σ at hb
  unfold finiteDensityWeight
  linarith

end CH2QRH
