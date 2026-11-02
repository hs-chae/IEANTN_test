/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Result
import FKS2Table4.Consumer
import RefinedResult
import IEANTN.Nodes.FKS2.v6.Conclusions

namespace FKS2Table4

theorem assembled (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    FKS2Numerics.v5.numerical_pi ∧ FKS2.v7.absolute_pi_bound ∧
      FKS2.v7.strict_allowance_improvement := by
  have hpsi : QRHCH2.v5.psi_refined_bound :=
    CH2QRH.refined_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs hrvm hsmall hlow hH hqrh
  have hnum : FKS2Numerics.v5.numerical_pi := numerical_pi hpsi hOld
  exact ⟨hnum,FKS2.v7.challenge_absolute_pi_bound hnum,
    FKS2.v7.challenge_strict_allowance_improvement⟩

#print assembled
#print axioms assembled
end FKS2Table4
