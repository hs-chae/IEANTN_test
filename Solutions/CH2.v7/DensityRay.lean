/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityOuterResult
import DensityError

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

/-- Normalize the actual spectral density bound, including its outer integral. -/
theorem densitySpectralBound_normalized {t x : ℝ} (hx : 0 < x) :
    densitySpectralBound t x * x ^ ((1 : ℝ) / 8) =
      Real.exp (-Real.log x / 8) * spectralBound t + Real.log x *
        (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ),
          Real.exp (-Real.log x * (7 / 8 - σ)) * finiteDensityWeight σ t) := by
  have hpow : x ^ (-(1 : ℝ) / 4) * x ^ ((1 : ℝ) / 8) = Real.exp (-Real.log x / 8) := by
    rw [← Real.rpow_add hx, Real.rpow_def_of_pos hx]
    congr 1; ring
  have hInt : (∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * finiteDensityWeight σ t) *
      x ^ ((1 : ℝ) / 8) = ∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ),
        Real.exp (-Real.log x * (7 / 8 - σ)) * finiteDensityWeight σ t := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro σ _
    dsimp only
    rw [show (x ^ (σ - 1) * finiteDensityWeight σ t) * x ^ ((1 : ℝ) / 8) =
        (x ^ (σ - 1) * x ^ ((1 : ℝ) / 8)) * finiteDensityWeight σ t by ring,
      ← Real.rpow_add hx, Real.rpow_def_of_pos hx]
    congr 1; congr 1; ring
  unfold densitySpectralBound
  rw [add_mul]
  calc
    _ = (x ^ (-(1 : ℝ) / 4) * x ^ ((1 : ℝ) / 8)) * spectralBound t +
        Real.log x * ((∫ σ in (3 / 4 : ℝ)..(7 / 8 : ℝ), x ^ (σ - 1) * finiteDensityWeight σ t) *
          x ^ ((1 : ℝ) / 8)) := by ring
    _ = _ := by rw [hpow, hInt]

/-- Uniform control of the actual selected-height count polynomial by its row endpoint. -/
theorem density_count_base_row {L₀ L τ t : ℝ} (hL0 : 64 ≤ L₀) (hL : L₀ ≤ L)
    (hτ : 44 ≤ τ) (ht0 : 1 ≤ t)
    (htlog : Real.log t ≤ τ / L₀ * L + (1 : ℝ) / 10 ^ (9 : ℕ)) :
    Real.exp (-L / 8) * spectralBound t ≤
      Real.exp (-L₀ / 8) * ((τ + (1 : ℝ) / 10 ^ (9 : ℕ)) ^ (2 : ℕ) / (2 * Real.pi) +
        (2 + 1 / Real.pi) * (τ + (1 : ℝ) / 10 ^ (9 : ℕ))) := by
  have hL00 : 0 < L₀ := by linarith
  let v := τ / L₀ + ((1 : ℝ) / 10 ^ (9 : ℕ)) / L₀
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvL0 : v * L₀ = τ + (1 : ℝ) / 10 ^ (9 : ℕ) := by dsimp [v]; field_simp
  have hlog : Real.log t ≤ v * L := by
    have hh := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ ((1 : ℝ) / 10 ^ (9 : ℕ)) / L₀ by positivity)
    have he : ((1 : ℝ) / 10 ^ (9 : ℕ)) / L₀ * L₀ = (1 : ℝ) / 10 ^ (9 : ℕ) := by field_simp
    rw [he] at hh
    dsimp [v]; nlinarith
  have hcount : spectralBound t ≤ (v * L) ^ (2 : ℕ) / (2 * Real.pi) + (2 + 1 / Real.pi) * (v * L) := by
    unfold spectralBound
    have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht0
    gcongr
  have hh := (mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le).trans
    (density_polynomial_base_uniform hL0 hL hv)
  simpa only [hvL0] using hh

theorem density_row_normalized (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk_ : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hFKS : FKS.v3.density_0618)
    (hRH : IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)))
    {L₀ τ x : ℝ} (hL0 : 64 ≤ L₀) (hτ : 44 ≤ τ)
    (hk0 : τ ≤ (7 / 10) * L₀) (hsep0 : 34 ≤ τ - L₀ / 8)
    (hx : Real.exp L₀ ≤ x) (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) :
    IEANTN.Eψ x * x ^ ((1 : ℝ) / 8) ≤ densityRowCertificate L₀ τ := by
  have hx0 : 0 < x := (Real.exp_pos L₀).trans_le hx
  let L := Real.log x
  let k := τ / L₀
  let T := Real.exp (k * L) + 1 / 2
  have hL00 : 0 < L₀ := by linarith
  have hL : L₀ ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos L₀) hx
    simpa [L] using hh
  have hL64 : 64 ≤ Real.log x := hL0.trans hL
  have hk : k ≤ 7 / 10 := (div_le_iff₀ hL00).mpr hk0
  have hkL0 : k * L₀ = τ := by dsimp [k]; field_simp
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hslope : 0 ≤ k - 1 / 8 := by nlinarith
  have hsep : 34 ≤ k * Real.log x - Real.log x / 8 := by
    have hh := mul_le_mul_of_nonneg_left hL hslope
    dsimp [L] at hh
    nlinarith
  obtain ⟨hTlo, hR, hxlo, _, _, hlogT⟩ := density_height_parameters hx0 hL64 hk hsep
  obtain ⟨t, ht, hE⟩ := density_finite_transfer hfe hdig h24u h24l hk_ hneg h2v hv hcs
    hrvm hsmall hlow hH hFKS hRH hTlo hR hxlo (by linarith) hqrh
  have htexp : Real.exp τ ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hL hkpos.le
    rw [hkL0] at hh
    have he := Real.exp_le_exp.mpr hh
    linarith [ht.1]
  have hτH : 3 * (10 : ℝ) ^ (12 : ℕ) ≤ Real.exp τ := by
    have hh := (CH2Section7A.exp_nat_bounds 44).1
    have he := Real.exp_le_exp.mpr hτ
    norm_num at hh ⊢; linarith
  have ht1 : 1 ≤ t := (show 1 ≤ Real.exp τ by rw [Real.one_le_exp_iff]; linarith).trans htexp
  have htlog : Real.log t ≤ τ / L₀ * L + (1 : ℝ) / 10 ^ (9 : ℕ) := by
    have htT : t ≤ T := ht.2
    have hh := Real.log_le_log (by linarith : 0 < t) htT
    exact hh.trans hlogT
  have hbase := density_count_base_row hL0 hL hτ ht1 htlog
  have houter := density_outer_grid_uniform hL0 hL (by linarith : 28 ≤ τ) hτH htexp
  have hrem := density_remainder_coefficient hx0 hL64 hk hsep
  have hscaled := mul_le_mul_of_nonneg_right hE (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 8)).le
  rw [add_mul, densitySpectralBound_normalized hx0] at hscaled
  unfold densityRowCertificate
  change _ ≤ densityGridCertificate L₀ τ + _ + _
  exact hscaled.trans (by dsimp [L] at *; linarith only [hbase, houter, hrem])

end CH2QRH

#print axioms CH2QRH.density_row_normalized
