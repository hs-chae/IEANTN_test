/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.OldProvider
import FKS2PairQRH
import FKS2PairConsumers
import FKS2Table4.Replay

theorem FKS2Pair.assembled
    (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hOld : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v6.old_pi ∧ FKS2Numerics.v7.qrh_pi ∧
    FKS2.v9.paired_absolute_pi ∧ FKS2.v9.strict_reconstructed_improvement ∧
    FKS2.v9.strict_historical_improvement ∧ FKS2.v9.exact_allowance_ratios := by
  have hOldPi := FKS2Numerics.v6.challenge_old_pi h300 h310 h320 h330 hOld
  have hpsi := CH2QRH.refined_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH hqrh
  have hNewPi := FKS2Numerics.v7.challenge_qrh_pi hpsi hOld
  exact ⟨hOldPi,hNewPi,FKS2.v9.challenge_paired_absolute_pi hOldPi hNewPi,
    FKS2.v9.challenge_strict_reconstructed_improvement,
    FKS2.v9.challenge_strict_historical_improvement,FKS2.v9.challenge_exact_allowance_ratios⟩
