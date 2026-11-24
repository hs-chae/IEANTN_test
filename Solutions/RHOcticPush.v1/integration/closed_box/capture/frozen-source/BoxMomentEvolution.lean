import BoxMomentNode
import BoxZeroEstimate
import BoxImproved
import IEANTN.Nodes.RHSmoothing.v2.Conclusions
import IEANTN.Nodes.Lcm.v5.Conclusions

/-! Additive actual consumers. Both original Mellin predicates are constructed
internally from their canonical no-argument providers. The earlier one-moment
partial interfaces remain available for historical comparison. The frozen
original four-input theorems and619-source study remain unchanged. -/
namespace RHOcticPush.BoxMoments
open Real
set_option maxHeartbeats 0

theorem psi_from_remaining_second (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hs : BoxMellinInputs.v1.second_moment_identity) : RHSmoothing.v2.box_psi :=
  BoxTail.actual_psi_improved rh he hz BoxMellinInputs.v2.challenge_first_moment hs

theorem lcm_from_remaining_second (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hs : BoxMellinInputs.v1.second_moment_identity) : Lcm.v5.box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using
    psi_from_remaining_second rh he hz hs (n:ℝ) hn

theorem pi_from_remaining_second (rh : SharedRH.hypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hs : BoxMellinInputs.v1.second_moment_identity)
    (hGM : RHContinuation.Ramanujan.GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    |IEANTN.primeCounting (exp L)-IEANTN.Li (exp L)| ≤
      RHLimit.PurePi.envelope BoxTail.improvedBound L + 2 :=
  BoxTail.actual_pi_Li_improved rh he hz BoxMellinInputs.v2.challenge_first_moment hs hGM hP hJ hL

#print axioms psi_from_remaining_second
#print axioms lcm_from_remaining_second
#print axioms pi_from_remaining_second
/-- Both actual Mellin predicates are now constructed in the proof body.
The exact original Box explicit formula and zero estimate remain explicit. -/
theorem actual_psi_closed_moments (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate) : RHSmoothing.v2.box_psi :=
  BoxTail.actual_psi_improved rh he hz BoxMellinInputs.v2.challenge_first_moment BoxMellinInputs.v2.challenge_second_moment_identity

theorem actual_lcm_closed_moments (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate) : Lcm.v5.box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using
    actual_psi_closed_moments rh he hz (n:ℝ) hn

theorem actual_pi_closed_moments (rh : SharedRH.hypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hGM : RHContinuation.Ramanujan.GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    |IEANTN.primeCounting (exp L)-IEANTN.Li (exp L)| ≤
      RHLimit.PurePi.envelope BoxTail.improvedBound L + 2 :=
  BoxTail.actual_pi_Li_improved rh he hz BoxMellinInputs.v2.challenge_first_moment
    BoxMellinInputs.v2.challenge_second_moment_identity hGM hP hJ hL

/-- The zero estimate and both exact moments are now constructed internally.
Only the original averaged EF remains a direct Box input. -/
theorem actual_psi_remaining_explicit_formula (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate) : RHSmoothing.v2.box_psi :=
  actual_psi_closed_moments rh he (RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB)

theorem actual_lcm_remaining_explicit_formula (rh : RiemannHypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate) : Lcm.v5.box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using
    actual_psi_remaining_explicit_formula rh he hN hB (n:ℝ) hn

theorem actual_pi_remaining_explicit_formula (rh : SharedRH.hypothesis)
    (he : RHSmoothingInputs.v1.box_explicit_formula)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (hGM : RHContinuation.Ramanujan.GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    |IEANTN.primeCounting (exp L)-IEANTN.Li (exp L)| ≤
      RHLimit.PurePi.envelope BoxTail.improvedBound L + 2 :=
  actual_pi_closed_moments rh he (RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB)
    hGM hP hJ hL

#print axioms actual_psi_remaining_explicit_formula
#print axioms actual_lcm_remaining_explicit_formula
#print axioms actual_pi_remaining_explicit_formula
#print axioms actual_psi_closed_moments
#print axioms actual_lcm_closed_moments
#print axioms actual_pi_closed_moments
end RHOcticPush.BoxMoments
