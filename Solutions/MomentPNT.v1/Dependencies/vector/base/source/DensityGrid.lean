/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityParameters
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Closed cell mass, retaining the positive slope decomposition used for continuation. -/
theorem laplace_cell_mass {L a b : ℝ} (hL : L ≠ 0) :
    (∫ y in a..b, Real.exp (-L * y)) =
      (Real.exp (-L * a) - Real.exp (-L * b)) / L := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hL), integral_exp]
  ring

/-- The spectral-count polynomial decays after normalizing by x^(1/8), on the entire row ray. -/
theorem density_polynomial_base_uniform {L₀ L v : ℝ} (hL0 : 64 ≤ L₀) (hL : L₀ ≤ L) (hv : 0 ≤ v) :
    Real.exp (-L / 8) * ( (v * L) ^ (2 : ℕ) / (2 * Real.pi) + (2 + 1 / Real.pi) * (v * L)) ≤
      Real.exp (-L₀ / 8) * ((v * L₀) ^ (2 : ℕ) / (2 * Real.pi) + (2 + 1 / Real.pi) * (v * L₀)) := by
  have hL00 : 0 < L₀ := by linarith
  have hH : 1 < Real.exp L₀ := Real.one_lt_exp_iff.mpr hL00
  have hdecay : (7 / 8 : ℝ) - 1 + 2 / Real.log (Real.exp L₀) ≤ 0 := by
    rw [Real.log_exp]
    have hh : (2 : ℝ) / L₀ ≤ 1 / 8 := by apply (div_le_iff₀ hL00).mpr; linarith
    linarith
  have hdecay1 : (7 / 8 : ℝ) - 1 + 1 / Real.log (Real.exp L₀) ≤ 0 := by
    rw [Real.log_exp] at *
    have hh : (1 : ℝ) / L₀ ≤ 2 / L₀ := by gcongr; norm_num
    linarith
  have h1 := power_log_boundary_antitone (p := 7 / 8) (q := 1) hH (by norm_num) hdecay1
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (Real.exp_le_exp.mpr hL)) (Real.exp_le_exp.mpr hL)
  have h2 := power_log_boundary_antitone (p := 7 / 8) (q := 2) hH (by norm_num) hdecay
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (Real.exp_le_exp.mpr hL)) (Real.exp_le_exp.mpr hL)
  norm_num only [Real.log_exp, Real.rpow_one, Real.rpow_two] at h1 h2
  rw [← Real.exp_mul] at h1 h2
  rw [← Real.exp_mul] at h1 h2
  have hc1 : 0 ≤ (2 + 1 / Real.pi) * v := by positivity
  have hc2 : 0 ≤ v ^ (2 : ℕ) / (2 * Real.pi) := by positivity
  have hh := add_le_add (mul_le_mul_of_nonneg_left h2 hc2) (mul_le_mul_of_nonneg_left h1 hc1)
  convert hh using 1 <;> congr 1 <;> ring

/-- Nonnegativity of the closed endpoint envelope on the actual real-part interval. -/
theorem densityFixedEnvelope_nonneg {σ τ : ℝ} (hσ : 3 / 4 ≤ σ) (hσ' : σ ≤ 7 / 8) (hτ : 28 ≤ τ) :
    0 ≤ densityFixedEnvelope σ τ := by
  have hr : 0 < 1 - 8 * (1 - σ) / 3 := by linarith
  have hq0 : 0 ≤ 5 - 2 * σ := by linarith
  have hq1 : 0 ≤ 5 - 2 * σ - 1 := by linarith
  have hq2 : 0 ≤ 5 - 2 * σ - 2 := by linarith
  have hq3 : 0 ≤ 5 - 2 * σ - 3 := by linarith
  have hl : 0 < Real.log (3 * (10 : ℝ) ^ (12 : ℕ)) := by linarith [log_verified_height_ge_twenty_eight]
  have hlt : 0 < Real.log (Real.exp τ) := by rw [Real.log_exp]; linarith
  unfold densityFixedEnvelope densityMomentMain fksDensityMajorant
  dsimp only
  positivity

/-- The explicit finite numerical expression to be kernel-certified for each row. -/
noncomputable def densityGridCertificate (L τ : ℝ) : ℝ :=
  densityFixedEnvelope (7 / 8) τ +
    ∑ i ∈ Finset.range 512,
      (densityFixedEnvelope (7 / 8 - (i + 1 : ℝ) / 4096) τ -
        densityFixedEnvelope (7 / 8 - (i : ℝ) / 4096) τ) * 4096 *
          (Real.exp (-L * (i : ℝ) / 4096) - Real.exp (-L * (i + 1 : ℝ) / 4096)) / L

/-- The complete row envelope, with a uniform positive allowance for all contour terms. -/
noncomputable def densityRowCertificate (L τ : ℝ) : ℝ :=
  densityGridCertificate L τ + Real.exp (-L / 8) *
    ((τ + (1 : ℝ) / 10 ^ (9 : ℕ)) ^ (2 : ℕ) / (2 * Real.pi) +
      (2 + 1 / Real.pi) * (τ + (1 : ℝ) / 10 ^ (9 : ℕ))) + (1 : ℝ) / 10 ^ (12 : ℕ)

end CH2QRH
