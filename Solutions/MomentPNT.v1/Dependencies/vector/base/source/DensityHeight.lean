/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityConvex

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- The density boundary decreases in height once its logarithmic derivative is nonpositive. -/
theorem power_log_boundary_antitone {p q H : ℝ} (hH : 1 < H) (hq : 0 ≤ q)
    (hdecay : p - 1 + q / Real.log H ≤ 0) :
    AntitoneOn (fun u : ℝ ↦ u ^ (p - 1) * Real.log u ^ q) (Set.Ici H) := by
  have hder : ∀ u ∈ Set.Ici H,
      HasDerivAt (fun u : ℝ ↦ u ^ (p - 1) * Real.log u ^ q)
        (u ^ (p - 2) * Real.log u ^ q * (p - 1 + q / Real.log u)) u := by
    intro u hu; exact hasDerivAt_power_log_tail (hH.trans_le hu)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici H)
    (fun u hu ↦ (hder u hu).continuousAt.continuousWithinAt)
    (fun u hu ↦ (hder u (interior_subset hu)).hasDerivWithinAt)
  intro u hu
  have hHu : H ≤ u := interior_subset hu
  have hu1 : 1 < u := hH.trans_le hHu
  have hu0 : 0 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hr := div_le_div_of_nonneg_left hq (Real.log_pos hH)
    (Real.log_le_log (by linarith : 0 < H) hHu)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

/-- In the actual real-part strip, both terms of FKS divided by height decrease above exp28. -/
theorem fks_density_boundary_antitone {σ H : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (hH : 1 < H) (hlH : 28 ≤ Real.log H) :
    AntitoneOn (fun u : ℝ ↦ fksDensityMajorant σ u / u) (Set.Ici H) := by
  have hl0 : 0 < Real.log H := by linarith
  have hq : 0 ≤ 5 - 2 * σ := by linarith
  have hratio : (5 - 2 * σ) / Real.log H ≤ 1 / 8 := by
    apply (div_le_iff₀ hl0).mpr; linarith
  have hratio2 : (2 : ℝ) / Real.log H ≤ 1 / 14 := by
    apply (div_le_iff₀ hl0).mpr; linarith
  have h1 := power_log_boundary_antitone (p := 8 * (1 - σ) / 3) hH hq (by linarith)
  have h2 := power_log_boundary_antitone (p := 0) (q := 2) hH (by norm_num) (by linarith)
  intro u hu v hv huv
  have hu0 : 0 < u := by have : H ≤ u := hu; linarith
  have hv0 : 0 < v := by have : H ≤ v := hv; linarith
  have hh1 := h1 hu hv huv
  have hh2 := h2 hu hv huv
  have he : ∀ u : ℝ, 0 < u → fksDensityMajorant σ u / u =
      9.795 * (u ^ (8 * (1 - σ) / 3 - 1) * Real.log u ^ (5 - 2 * σ)) +
        4.465 * (u ^ (-1 : ℝ) * Real.log u ^ (2 : ℕ)) := by
    intro u hu0
    simp only [fksDensityMajorant, Real.rpow_sub hu0, Real.rpow_one, Real.rpow_neg_one]
    ring
  change fksDensityMajorant σ v / v ≤ fksDensityMajorant σ u / u
  rw [he u hu0, he v hv0]
  norm_num [Real.rpow_two] at hh2
  nlinarith

/-- Fixed lower-height envelope, independent of the later x and selected CH2 height. -/
noncomputable def densityFixedEnvelope (σ τ : ℝ) : ℝ :=
  2 * (9.795 * densityMomentMain σ (3 * (10 : ℝ) ^ (12 : ℕ)) +
    4.465 * ((Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) ^ (2 : ℕ) +
      2 * Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) + 2) / (3 * (10 : ℝ) ^ (12 : ℕ)))) +
    4 * Real.pi * (fksDensityMajorant σ (Real.exp τ) / Real.exp τ)

/-- Uniform validity of the certified envelope at every later admissible height. -/
theorem finiteDensityWeight_le_fixed {σ τ t : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8)
    (hτ : 28 ≤ τ) (hτH : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ Real.exp τ) (ht : Real.exp τ ≤ t) :
    finiteDensityWeight σ t ≤ densityFixedEnvelope σ τ := by
  have hbound := finiteDensityWeight_le_moments hσ hσ' (hτH.trans ht)
  have hB := fks_density_boundary_antitone hσ hσ'
    (show 1 < Real.exp τ by rw [Real.one_lt_exp_iff]; linarith)
    (by simpa using hτ)
  have hh := hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hp : 0 ≤ 4 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hh hp
  unfold densityFixedEnvelope
  apply hbound.trans
  convert add_le_add_right hmul _ using 1 <;> first | rfl | ring

/-- The finite moment envelope decreases as the real-part cutoff moves to the right. -/
theorem densityMomentMain_antitone {H : ℝ} (hH : 1 ≤ H) (hlog : 1 ≤ Real.log H) :
    AntitoneOn (fun σ ↦ densityMomentMain σ H) (Set.Icc (3 / 4) (7 / 8)) := by
  intro σ hσ τ hτ hστ
  have hrσ : 0 < 1 - 8 * (1 - σ) / 3 := by linarith [hσ.1]
  have hrτ : 0 < 1 - 8 * (1 - τ) / 3 := by linarith [hτ.1]
  have hl : 0 < Real.log H := by linarith
  have hqτ : 0 ≤ 5 - 2 * τ - 3 := by linarith [hτ.2]
  have hqσ0 : 0 ≤ 5 - 2 * σ := by linarith [hσ.2]
  have hqσ1 : 0 ≤ 5 - 2 * σ - 1 := by linarith [hσ.2]
  have hqσ2 : 0 ≤ 5 - 2 * σ - 2 := by linarith [hσ.2]
  have hqσ3 : 0 ≤ 5 - 2 * σ - 3 := by linarith [hσ.2]
  have hqτ0 : 0 ≤ 5 - 2 * τ := by linarith [hτ.2]
  have hqτ1 : 0 ≤ 5 - 2 * τ - 1 := by linarith [hτ.2]
  have hqτ2 : 0 ≤ 5 - 2 * τ - 2 := by linarith [hτ.2]
  have hqτ3 : 0 ≤ 5 - 2 * τ - 3 := by linarith [hτ.2]
  unfold densityMomentMain
  dsimp only
  gcongr <;> first | positivity | linarith [hσ.1, hσ.2, hτ.1, hτ.2]

/-- The fixed-height majorant is decreasing in real part throughout the actual density strip. -/
theorem densityFixedEnvelope_antitone {τ : ℝ} (hτ : 28 ≤ τ) :
    AntitoneOn (fun σ ↦ densityFixedEnvelope σ τ) (Set.Icc (3 / 4) (7 / 8)) := by
  intro σ hσ σ' hσ' hσσ'
  have hH : (1 : ℝ) ≤ 3 * (10 : ℝ) ^ (12 : ℕ) := by norm_num
  have hlH : 1 ≤ Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) := by linarith [log_verified_height_ge_twenty_eight]
  have hM := densityMomentMain_antitone hH hlH hσ hσ' hσσ'
  have he1 : 1 ≤ Real.exp τ := Real.one_le_exp (by linarith)
  have hl1 : 1 ≤ Real.log (Real.exp τ) := by rw [Real.log_exp]; linarith
  have hF : fksDensityMajorant σ' (Real.exp τ) ≤ fksDensityMajorant σ (Real.exp τ) := by
    unfold fksDensityMajorant
    gcongr <;> linarith [hσ.2, hσ'.2]
  have hF' := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hF (Real.exp_pos τ).le)
    (by positivity : 0 ≤ 4 * Real.pi)
  unfold densityFixedEnvelope
  dsimp only at *
  exact add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 9.795)) _)
      (by norm_num : (0 : ℝ) ≤ 2)) hF'

end CH2QRH
