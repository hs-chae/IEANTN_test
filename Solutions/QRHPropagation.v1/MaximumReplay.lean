/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Applications
import DudekCriterionReplay
import Exports
import FKS2PipelineReplay
import PrimeIntervalReplay
import ZeroFreeHeightReplay
import IEANTN.Nodes.QRHPropagation.v1.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v5.Conclusions
import IEANTN.Nodes.DudekPlatt.v5.Conclusions
import IEANTN.Bridges.QRH.Consequences
import IEANTN.Bridges.QRH.Geometry
import IEANTN.Bridges.QRH.ExistingRegions
import IEANTN.Bridges.QRH.Identities

/-! Replay the new Ramanujan route from original CH2 source statements and QRH.
The actual existing Dudek--Platt criterion proof is imported through a source-identical alias. -/

theorem QRHMaxReplay.ramanujan (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths) :
    ∀ x : ℝ, Real.exp 401 < x →
      IEANTN.primeCounting x ^ 2 < Real.exp 1 * x / Real.log x *
        IEANTN.primeCounting (x / Real.exp 1) :=
  QRHPropagation.ramanujan
    ((CH2QRH.refined_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
      hrvm hsmall hlow hH) hqrh) DudekPlatt.v3.challenge_criterion

#print axioms QRHMaxReplay.ramanujan

/-- All new non-density arithmetic consumers replay from the original thirteen source inputs.
Neither the new psi transfer nor any reused integration/criterion theorem is a premise. -/
theorem QRHMaxReplay.arithmetic (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
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
    (hqrh : OpenAIQRH.v1.zeta_seven_eighths) :
    QRHPropagation.v1.theta_power_bound ∧ QRHPropagation.v1.pi_power_bound ∧
    QRHPropagation.v1.short_prime_intervals ∧ QRHPropagation.v1.fks2_classical_replay ∧
    DudekPlattNumerics.v5.pi_two_sided_qrh ∧ DudekPlatt.v5.ramanujan_401 := by
  have hpsi := (CH2QRH.refined_transfer_proved hfe hdig h24u h24l hk hneg h2v hv hcs
    hrvm hsmall hlow hH) hqrh
  have ht := QRHExports.theta_power hpsi
  exact ⟨ht, QRHPiPower.pi_bound ht,
    QRHExports.moving_intervals ht PrimeInterval.v1.challenge_eTheta_criterion,
    QRHPiPower.fks2_replay FKS2.v2.challenge_theorem_3 ht,
    (fun _ hx ↦ QRHPropagation.pi_expansion hpsi hx),
    QRHPropagation.ramanujan hpsi DudekPlatt.v3.challenge_criterion⟩

/-- The independent zero-geometry/identity branch uses no CH2 or density transfer. -/
theorem QRHMaxReplay.geometry (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hRH : PlattTrudgian.v1.rh_up_to)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions) :
    QRHConsequences.v1.density_vanishes ∧ QRHConsequences.v1.reciprocal_differentiable ∧
    QRHConsequences.v1.classical_region ∧ QRHConsequences.v1.all_height_classical_region ∧
    RosserSchoenfeld.v1.zero_free_region ∧ ZetaHadamard.v2.halfplane_partial_fractions ∧
    ZetaLogDeriv.v2.halfplane_functional_equation :=
  ⟨QRHConsequencesProof.density_vanishes hqrh (fun _ _ _ h hσ ↦ QRHGeometry.density_vanishes h hσ),
   QRHConsequencesProof.reciprocal_differentiable hqrh
     (fun _ h ↦ QRHGeometry.reciprocal_differentiable h),
   QRHConsequencesProof.classical_region hqrh
     (fun _ _ _ hβ hR ht hc h ↦ QRHGeometry.classical_region hβ hR ht hc h)
     ZeroFreeHeight.v1.challenge_classical_region_descends hRH,
   QRHConsequencesProof.all_height_classical_region hqrh
     (fun _ _ _ hβ hR ht hc h ↦ QRHGeometry.classical_region hβ hR ht hc h)
     ZeroFreeHeight.v1.challenge_classical_region_descends hRH,
   QRHExistingRegions.rosser_schoenfeld hqrh hRH,
   QRHIdentities.partial_fractions hqrh hH, QRHIdentities.functional_equation hqrh hfe⟩

#print axioms QRHMaxReplay.arithmetic
#print axioms QRHMaxReplay.geometry
