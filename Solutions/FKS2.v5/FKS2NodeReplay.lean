/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2UpdatedSolution
import RefinedResult
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions

theorem FKS2NodeReplay.updated_from_psi (hpsi : QRHCH2.v5.psi_refined_bound)
    (hB : BKLNW.v1.corollary_5_1) :
    QRHPropagation.v3.psi_classical_bound ∧ FKS2.v5.updated_theta ∧
    FKS2.v5.updated_intervals ∧ FKS2.v5.strict_improvement := by
  have hp := FKS2QRHAdapter.psi_same_shape hpsi
  have hn := FKS2Update.updated_provider
  exact ⟨hp,FKS2.v5.challenge_updated_theta hp hB hn,
    FKS2.v5.challenge_updated_intervals hp hB hn,FKS2.v5.challenge_strict_improvement⟩

theorem FKS2NodeReplay.qrh_to_updated_fks2 (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper) (h24l : CH2.v2.proposition_2_4_lower)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hneg : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2v : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hB : BKLNW.v1.corollary_5_1) :
    QRHPropagation.v3.psi_classical_bound ∧ FKS2.v5.updated_theta ∧
    FKS2.v5.updated_intervals ∧ FKS2.v5.strict_improvement := by
  have hpsi : QRHCH2.v5.psi_refined_bound :=
    CH2QRH.refined_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hqrh
  exact updated_from_psi hpsi hB

theorem FKS2NodeReplay.baseline (hF : FKS.v2.psi_classical_bound)
    (hB : BKLNW.v1.corollary_5_1) :
    FKS2.v4.baseline_theta ∧ FKS2.v4.baseline_intervals := by
  exact ⟨FKS2Correction.baseline_theta hF hB,FKS2Correction.baseline_intervals hF hB⟩

#print FKS2NodeReplay.updated_from_psi
#print FKS2NodeReplay.qrh_to_updated_fks2
#print axioms FKS2NodeReplay.qrh_to_updated_fks2
#print axioms FKS2NodeReplay.baseline
