/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityRay
import DensityExpForm
import IEANTN.Nodes.CH2.v6.Conclusions

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- Exact finite arithmetic and domain obligations for one unchanged frontier row. -/
def densityRowAdmissible (L τ C : ℝ) : Prop :=
  64 ≤ L ∧ 44 ≤ τ ∧ τ ≤ (7 / 10) * L ∧ 34 ≤ τ - L / 8 ∧ densityRowCertificate L τ ≤ C

/-- These are closed numerical obligations, not an additional analytic or PNT source input. -/
def densityFrontierCertificate : Prop :=
  ∀ L C : ℝ, (L, C) ∈ CH2.v6.densityFrontier → ∃ τ : ℝ, densityRowAdmissible L τ C

theorem density_row_bound (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    {L τ C x : ℝ} (hrow : densityRowAdmissible L τ C)
    (hx : Real.exp L ≤ x) (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7 / 8)) :
    IEANTN.Eψ x ≤ C * x ^ (-(1 : ℝ) / 8) := by
  obtain ⟨hL, hτ, hk, hsep, hcert⟩ := hrow
  have hx0 : 0 < x := (Real.exp_pos L).trans_le hx
  have hp := density_row_normalized hfe hdig h24u h24l hk_ hneg h2v hv hcs hrvm hsmall hlow hH
    hFKS hRH hL hτ hk hsep hx hqrh
  have hinv : x ^ (-(1 : ℝ) / 8) = 1 / x ^ ((1 : ℝ) / 8) := by
    rw [show (-(1 : ℝ) / 8) = -((1 : ℝ) / 8) by ring, Real.rpow_neg hx0.le]
    simp only [one_div]
  rw [hinv, mul_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 8))).mpr
  exact hp.trans hcert

theorem density_transfer_of_certificates (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hcert : densityFrontierCertificate) : CH2.v6.density_transfer := by
  intro hFKS hRH hqrh L C hLC x hx
  obtain ⟨τ, hrow⟩ := hcert L C hLC
  exact density_row_bound hfe hdig h24u h24l hk_ hneg h2v hv hcs hrvm hsmall hlow hH
    hFKS hRH hrow hx hqrh

end CH2QRH
#print axioms CH2QRH.density_transfer_of_certificates
