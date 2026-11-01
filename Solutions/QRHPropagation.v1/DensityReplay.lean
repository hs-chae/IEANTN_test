/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityCertificates
import DensityApplications
import TableReplay
import PrimeIntervalReplay
import IEANTN.Nodes.QRHPropagation.v1.Conclusions
import IEANTN.Nodes.BKLNW.v3.Conclusions

/-- Complete density-consumer replay, including the original checked numeric certificates.
The only extra analytic inputs are the explicit corrected FKS density and finite-height RH. -/
theorem QRHMaxReplay.density (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hFKS : FKS.v3.density_0618) (hRH : PlattTrudgian.v1.rh_up_to) :
    QRHPropagation.v1.theta_density_bound ∧ QRHPropagation.v1.pi_density_bound ∧
    QRHPropagation.v1.density_prime_intervals ∧ BKLNW.v3.table8_qrh_replay := by
  have hpsi := (CH2QRH.density_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hFKS hRH hqrh
  have ht := QRHDensityApplications.theta_density hpsi
  exact ⟨ht, QRHDensityApplications.pi_density ht,
    QRHDensityApplications.intervals_density ht PrimeInterval.v1.challenge_eTheta_criterion,
    QRHTableReplay.table_updates hpsi⟩

#print axioms QRHMaxReplay.density
