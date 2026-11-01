/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Exports
import DensityApplications
import IEANTN.Nodes.QRHPropagation.v1.Conclusions

/-! Every conclusion is proved against its exact named input interface. -/
theorem QRHPropagation.v1.challenge_theta_power_bound
    (hpsi : QRHCH2.v5.psi_refined_bound) : QRHPropagation.v1.theta_power_bound :=
  QRHExports.theta_power hpsi

theorem QRHPropagation.v1.challenge_pi_power_bound
    (hθ : QRHPropagation.v1.theta_power_bound) : QRHPropagation.v1.pi_power_bound :=
  QRHPiPower.pi_bound hθ

theorem QRHPropagation.v1.challenge_short_prime_intervals
    (hθ : QRHPropagation.v1.theta_power_bound) (hc : PrimeInterval.v1.eTheta_criterion) :
    QRHPropagation.v1.short_prime_intervals := QRHExports.moving_intervals hθ hc

theorem QRHPropagation.v1.challenge_fks2_classical_replay
    (hθ : QRHPropagation.v1.theta_power_bound) (h3 : FKS2.v2.theorem_3) :
    QRHPropagation.v1.fks2_classical_replay := QRHPiPower.fks2_replay h3 hθ

theorem QRHPropagation.v1.challenge_theta_density_bound
    (hpsi : QRHCH2.v2.psi_density_frontier) : QRHPropagation.v1.theta_density_bound :=
  QRHDensityApplications.theta_density hpsi

theorem QRHPropagation.v1.challenge_pi_density_bound
    (hθ : QRHPropagation.v1.theta_density_bound) : QRHPropagation.v1.pi_density_bound :=
  QRHDensityApplications.pi_density hθ

theorem QRHPropagation.v1.challenge_density_prime_intervals
    (hθ : QRHPropagation.v1.theta_density_bound) (hc : PrimeInterval.v1.eTheta_criterion) :
    QRHPropagation.v1.density_prime_intervals := QRHDensityApplications.intervals_density hθ hc
