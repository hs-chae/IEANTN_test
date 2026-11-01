/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityResult
import CertData.DensityBlockResultRow64
import CertData.DensityBlockResultRow80
import CertData.DensityBlockResultRow96
import CertData.DensityBlockResultRow112
import CertData.DensityBlockResultRow128
import CertData.DensityBlockResultRow160
import CertData.DensityBlockResultRow192
import CertData.DensityBlockResultRow224
import CertData.DensityBlockResultRow256
import CertData.DensityBlockResultRow300
import CertData.DensityBlockResultRow512
import CertData.DensityBlockResultRow1000

namespace CH2QRH

/-- The numeric checker sees the exact analytic envelope, without a replacement input. -/
theorem densityNumericQ_eq (σ τ : ℝ) : DensityNumeric.Q σ τ = densityEnvelopeExpForm σ τ := by
  rfl

theorem density_row_64_certified : densityRowCertificate 64 44 ≤ 0.97500 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 44), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow64.endpoint_upper
  have h₁ := DensityBlockResultRow64.base_upper
  have h₂ := DensityBlockResultRow64.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_80_certified : densityRowCertificate 80 45 ≤ 0.23719 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 45), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow80.endpoint_upper
  have h₁ := DensityBlockResultRow80.base_upper
  have h₂ := DensityBlockResultRow80.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_96_certified : densityRowCertificate 96 47 ≤ 0.08349 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 47), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow96.endpoint_upper
  have h₁ := DensityBlockResultRow96.base_upper
  have h₂ := DensityBlockResultRow96.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_112_certified : densityRowCertificate 112 48 ≤ 0.04372 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 48), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow112.endpoint_upper
  have h₁ := DensityBlockResultRow112.base_upper
  have h₂ := DensityBlockResultRow112.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_128_certified : densityRowCertificate 128 50 ≤ 0.03013 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 50), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow128.endpoint_upper
  have h₁ := DensityBlockResultRow128.base_upper
  have h₂ := DensityBlockResultRow128.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_160_certified : densityRowCertificate 160 55 ≤ 0.02069 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 55), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow160.endpoint_upper
  have h₁ := DensityBlockResultRow160.base_upper
  have h₂ := DensityBlockResultRow160.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_192_certified : densityRowCertificate 192 61 ≤ 0.01713 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 61), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow192.endpoint_upper
  have h₁ := DensityBlockResultRow192.base_upper
  have h₂ := DensityBlockResultRow192.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_224_certified : densityRowCertificate 224 67 ≤ 0.01526 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 67), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow224.endpoint_upper
  have h₁ := DensityBlockResultRow224.base_upper
  have h₂ := DensityBlockResultRow224.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_256_certified : densityRowCertificate 256 73 ≤ 0.01411 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 73), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow256.endpoint_upper
  have h₁ := DensityBlockResultRow256.base_upper
  have h₂ := DensityBlockResultRow256.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_300_certified : densityRowCertificate 300 82 ≤ 0.01310 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 82), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow300.endpoint_upper
  have h₁ := DensityBlockResultRow300.base_upper
  have h₂ := DensityBlockResultRow300.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_512_certified : densityRowCertificate 512 140 ≤ 0.01117 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 140), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow512.endpoint_upper
  have h₁ := DensityBlockResultRow512.base_upper
  have h₂ := DensityBlockResultRow512.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

theorem density_row_1000_certified : densityRowCertificate 1000 260 ≤ 0.01014 := by
  unfold densityRowCertificate densityGridCertificate
  simp_rw [densityFixedEnvelope_eq_expForm (by norm_num : (28 : ℝ) ≤ 260), ← densityNumericQ_eq]
  have h₀ := DensityBlockResultRow1000.endpoint_upper
  have h₁ := DensityBlockResultRow1000.base_upper
  have h₂ := DensityBlockResultRow1000.sum_upper
  simp only [DensityNumeric.cellTerm] at h₂
  linarith

/-- Every original frontier row has a kernel-checked numerical certificate and admissible height. -/
theorem densityFrontier_certified : densityFrontierCertificate := by
  intro L C hLC
  simp only [CH2.v6.densityFrontier, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hLC
  rcases hLC with h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨44, by norm_num, by norm_num, by norm_num, by norm_num, density_row_64_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨45, by norm_num, by norm_num, by norm_num, by norm_num, density_row_80_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨47, by norm_num, by norm_num, by norm_num, by norm_num, density_row_96_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨48, by norm_num, by norm_num, by norm_num, by norm_num, density_row_112_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨50, by norm_num, by norm_num, by norm_num, by norm_num, density_row_128_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨55, by norm_num, by norm_num, by norm_num, by norm_num, density_row_160_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨61, by norm_num, by norm_num, by norm_num, by norm_num, density_row_192_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨67, by norm_num, by norm_num, by norm_num, by norm_num, density_row_224_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨73, by norm_num, by norm_num, by norm_num, by norm_num, density_row_256_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨82, by norm_num, by norm_num, by norm_num, by norm_num, density_row_300_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨140, by norm_num, by norm_num, by norm_num, by norm_num, density_row_512_certified⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨260, by norm_num, by norm_num, by norm_num, by norm_num, density_row_1000_certified⟩

theorem density_transfer_proved (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    : CH2.v6.density_transfer :=
  density_transfer_of_certificates hfe hdig h24u h24l hk_ hneg h2v hv hcs hrvm hsmall hlow hH
    densityFrontier_certified

end CH2QRH
#print axioms CH2QRH.densityFrontier_certified
#print axioms CH2QRH.density_transfer_proved
