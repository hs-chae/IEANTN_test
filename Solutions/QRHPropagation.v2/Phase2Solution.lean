/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS.v2.Conclusions
import IEANTN.Nodes.FKS2.v1.Conclusions
import Polynomial
import PartialSummation
import IntervalsSharp
import FKSQuantitative
import RamanujanPhase2
import ArithmeticPhase2
import TablesPhase2
import IEANTN.Nodes.QRHPropagation.v2.Conclusions
import IEANTN.Nodes.CH2.v10.Conclusions
import IEANTN.Nodes.QRHCH2.v6.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v6.Conclusions
import IEANTN.Nodes.DudekPlatt.v6.Conclusions
import IEANTN.Nodes.BKLNW.v4.Conclusions
import IEANTN.Nodes.PlattTrudgian2021.v2.Conclusions
import IEANTN.Nodes.Lcm.v3.Conclusions
import IEANTN.Nodes.Primorial.v1.Conclusions
import IEANTN.Nodes.FKS2.v3.Conclusions

theorem QRHPropagation.v2.challenge_theta_frontier
    (h0 : QRHCH2.v2.psi_density_frontier)
    : QRHPropagation.v2.theta_frontier := by
  exact QRHPhase2.theta_frontier h0

theorem QRHPropagation.v2.challenge_pi_density_300
    (h0 : QRHCH2.v2.psi_density_frontier)
    : QRHPropagation.v2.pi_density_300 := by
  exact QRHPhase2.pi_density_300 h0

theorem QRHPropagation.v2.challenge_prime_intervals_192
    (h0 : QRHCH2.v2.psi_density_frontier)
    (h1 : PrimeInterval.v1.eTheta_criterion)
    : QRHPropagation.v2.prime_intervals_192 := by
  exact QRHPhase2.intervals_192 h0 h1

theorem QRHPropagation.v2.challenge_prime_intervals_300
    (h0 : QRHCH2.v2.psi_density_frontier)
    (h1 : PrimeInterval.v1.eTheta_criterion)
    : QRHPropagation.v2.prime_intervals_300 := by
  exact QRHPhase2.intervals_300 h0 h1

theorem QRHPropagation.v2.challenge_classical_three
    (h0 : QRHCH2.v2.psi_density_frontier)
    : QRHPropagation.v2.classical_three := by
  exact ⟨QRHPhase2.psi_classical_300 h0, QRHPhase2.theta_classical_300 h0, QRHPhase2.pi_classical_300 h0⟩

theorem QRHPropagation.v2.challenge_mu_300
    (h0 : QRHCH2.v2.psi_density_frontier)
    : QRHPropagation.v2.mu_300 := by
  exact QRHPhase2.mu_300_le h0

theorem CH2.v10.challenge_polynomial_transfer
    (h0 : CH2.v2.proposition_2_4_upper)
    (h1 : CH2.v2.proposition_2_4_lower)
    (h2 : ZeroCount.v1.rvm_error_bound)
    (h3 : ZeroCount.v1.rvm_error_small)
    (h4 : ZetaHadamard.v1.logDeriv_partial_fractions)
    (h5 : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (h6 : ZetaLogDerivValues.v1.logDeriv_two)
    (h7 : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (h8 : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h9 : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (h10 : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h11 : CotangentSeries.v1.cot_series_zeta_values)
    (h12 : LowZeroes.v1.no_zeroes_below_first_ordinate)
    : CH2.v10.polynomial_transfer := by
  exact QRHPhase2.psi_polynomial_transfer h5 h10 h0 h1 h9 h8 h6 h7 h11 h2 h3 h12 h4

theorem QRHCH2.v6.challenge_psi_polynomial_bound
    (h0 : CH2.v10.polynomial_transfer)
    (h1 : OpenAIQRH.v1.zeta_seven_eighths)
    : QRHCH2.v6.psi_polynomial_bound := by
  exact h0 h1

theorem DudekPlattNumerics.v6.challenge_pi_two_sided_144
    (h0 : QRHCH2.v2.psi_density_frontier)
    : DudekPlattNumerics.v6.pi_two_sided_144 := by
  exact fun x hx ↦ QRHPhase2.pi_expansion_phase2 h0 hx

theorem DudekPlatt.v6.challenge_ramanujan_145
    (h0 : DudekPlattNumerics.v6.pi_two_sided_144)
    (h1 : DudekPlatt.v3.criterion)
    : DudekPlatt.v6.ramanujan_145 := by
  exact QRHPhase2.ramanujan_of_expansion h0 h1

theorem BKLNW.v4.challenge_table8_phase2
    (h0 : QRHCH2.v2.psi_density_frontier)
    : BKLNW.v4.table8_phase2 := by
  exact QRHPhase2.table8_phase2 h0

theorem PlattTrudgian2021.v2.challenge_numerical_profile
    (h0 : QRHCH2.v2.psi_density_frontier)
    : PlattTrudgian2021.v2.numerical_profile := by
  exact QRHPhase2.pt_phase2 h0

theorem Lcm.v3.challenge_log_growth
    (h0 : QRHCH2.v2.psi_density_frontier)
    : Lcm.v3.log_growth := by
  exact QRHPhase2.lcm_log_window h0

theorem Primorial.v1.challenge_log_growth
    (h0 : QRHCH2.v2.psi_density_frontier)
    : Primorial.v1.log_growth := by
  exact QRHPhase2.primorial_log_window h0

theorem FKS2.v3.challenge_psi_hybrid
    (h0 : QRHPropagation.v2.classical_three)
    (h1 : FKS.v2.psi_classical_bound)
    : FKS2.v3.psi_hybrid := by
  exact QRHPhase2.hybrid_classical h1 h0.1

theorem FKS2.v3.challenge_theta_hybrid
    (h0 : QRHPropagation.v2.classical_three)
    (h1 : FKS2.v1.corollary_14)
    : FKS2.v3.theta_hybrid := by
  exact QRHPhase2.hybrid_classical h1 h0.2.1

theorem FKS2.v3.challenge_pi_hybrid_22
    (h0 : QRHPropagation.v2.classical_three)
    (h1 : FKS2.v1.corollary_22)
    : FKS2.v3.pi_hybrid_22 := by
  exact QRHPhase2.hybrid_classical h1 h0.2.2

theorem FKS2.v3.challenge_pi_hybrid_23
    (h0 : QRHPropagation.v2.classical_three)
    (h1 : FKS2.v1.corollary_23)
    : FKS2.v3.pi_hybrid_23 := by
  exact QRHPhase2.hybrid_classical h1 h0.2.2

theorem FKS2.v3.challenge_pi_fks2_rounded
    (h0 : QRHCH2.v2.psi_density_frontier)
    (h1 : FKS2.v2.theorem_3)
    : FKS2.v3.pi_fks2_rounded := by
  exact QRHPhase2.fks_pi_from_correction (QRHPhase2.theta_classical_300 h0) (QRHPhase2.mu_300_le h0) h1
