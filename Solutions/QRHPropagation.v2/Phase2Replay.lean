import Phase2Solution
import DensityCertificates
import PrimeIntervalReplay
import DudekCriterionReplay
import FKS2PipelineReplay

/-! Connected replay retains the original thirteen analytic premises and the two density inputs.
QRH, transfer, corrections and arithmetic criteria are consumed by proof terms. -/
theorem QRHPhase2Replay.density (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    QRHCH2.v6.psi_polynomial_bound ∧ QRHPropagation.v2.theta_frontier ∧
    QRHPropagation.v2.pi_density_300 ∧ QRHPropagation.v2.prime_intervals_300 ∧
    QRHPropagation.v2.classical_three ∧ QRHPropagation.v2.mu_300 ∧
    DudekPlatt.v6.ramanujan_145 ∧ BKLNW.v4.table8_phase2 ∧
    PlattTrudgian2021.v2.numerical_profile ∧ Lcm.v3.log_growth ∧ Primorial.v1.log_growth := by
  have hpsi := (CH2QRH.density_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hFKS hRH hqrh
  have hp := (QRHPhase2.psi_polynomial_transfer hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hqrh
  exact ⟨hp, QRHPhase2.theta_frontier hpsi, QRHPhase2.pi_density_300 hpsi,
    QRHPhase2.intervals_300 hpsi PrimeInterval.v1.challenge_eTheta_criterion,
    ⟨QRHPhase2.psi_classical_300 hpsi, QRHPhase2.theta_classical_300 hpsi,
      QRHPhase2.pi_classical_300 hpsi⟩,
    QRHPhase2.mu_300_le hpsi,
    QRHPhase2.ramanujan_phase2 hpsi DudekPlatt.v3.challenge_criterion,
    QRHPhase2.table8_phase2 hpsi, QRHPhase2.pt_phase2 hpsi,
    QRHPhase2.lcm_log_window hpsi, QRHPhase2.primorial_log_window hpsi⟩

#print axioms QRHPhase2Replay.density
