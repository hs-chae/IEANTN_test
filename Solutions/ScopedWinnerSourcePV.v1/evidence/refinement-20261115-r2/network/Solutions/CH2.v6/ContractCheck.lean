/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BothSolutions

def original_paired_transfer_contract : Prop := ∀
    (ch2_v2_proposition_2_4_upper : CH2.v2.proposition_2_4_upper)
    (ch2_v2_proposition_2_4_lower : CH2.v2.proposition_2_4_lower)
    (ch2_v3_extremal_majorant : CH2.v3.extremal_majorant)
    (ch2_v3_extremal_minorant : CH2.v3.extremal_minorant)
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zerocount_v1_rvm_error_small : ZeroCount.v1.rvm_error_small)
    (zetahadamard_v1_logderiv_partial_fractions : ZetaHadamard.v1.logDeriv_partial_fractions)
    (zetalogderiv_v1_logderiv_functional_equation : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (zetalogderivvalues_v1_logderiv_two : ZetaLogDerivValues.v1.logDeriv_two)
    (zetalogderivvalues_v1_logderiv_three_halves : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (zetalogderivvalues_v1_logderiv_neg_one : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (zetalogderivvalues_v1_logderiv_laurent_alternating : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (gammaasymptotics_v2_digamma_sub_log_isbigo_strip : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (cotangentseries_v1_cot_series_zeta_values : CotangentSeries.v1.cot_series_zeta_values)
    (lowzeroes_v1_no_zeroes_below_first_ordinate : LowZeroes.v1.no_zeroes_below_first_ordinate),
    CH2.v6.paired_transfer

theorem exact_paired_transfer_contract : original_paired_transfer_contract :=
  CH2.v6.challenge_paired_transfer
#print axioms exact_paired_transfer_contract

def original_density_transfer_contract : Prop := ∀
    (ch2_v2_proposition_2_4_upper : CH2.v2.proposition_2_4_upper)
    (ch2_v2_proposition_2_4_lower : CH2.v2.proposition_2_4_lower)
    (ch2_v3_extremal_majorant : CH2.v3.extremal_majorant)
    (ch2_v3_extremal_minorant : CH2.v3.extremal_minorant)
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zerocount_v1_rvm_error_small : ZeroCount.v1.rvm_error_small)
    (zetahadamard_v1_logderiv_partial_fractions : ZetaHadamard.v1.logDeriv_partial_fractions)
    (zetalogderiv_v1_logderiv_functional_equation : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (zetalogderivvalues_v1_logderiv_two : ZetaLogDerivValues.v1.logDeriv_two)
    (zetalogderivvalues_v1_logderiv_three_halves : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (zetalogderivvalues_v1_logderiv_neg_one : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (zetalogderivvalues_v1_logderiv_laurent_alternating : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (gammaasymptotics_v2_digamma_sub_log_isbigo_strip : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (cotangentseries_v1_cot_series_zeta_values : CotangentSeries.v1.cot_series_zeta_values)
    (lowzeroes_v1_no_zeroes_below_first_ordinate : LowZeroes.v1.no_zeroes_below_first_ordinate),
    CH2.v6.density_transfer

theorem exact_density_transfer_contract : original_density_transfer_contract :=
  CH2.v6.challenge_density_transfer
#print axioms exact_density_transfer_contract

