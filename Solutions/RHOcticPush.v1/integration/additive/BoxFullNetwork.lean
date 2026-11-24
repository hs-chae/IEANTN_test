import BoxExplicitFormula
import BoxMomentNode
import BoxZeroEstimate
import NodeProviders
import PrimorialEvolution
import IEANTN.Nodes.IntegratedPerron.v1.Conclusions
import IEANTN.Nodes.BPTOffOrdinate.v1.Conclusions
import IEANTN.Nodes.RHSmoothingInputs.v2.Conclusions
import IEANTN.Nodes.RHSmoothing.v3.Conclusions
import IEANTN.Nodes.Lcm.v6.Conclusions
import IEANTN.Nodes.RHPrimeCounting.v4.Conclusions
import IEANTN.Nodes.Primorial.v4.Conclusions

/-! Complete actual Box analytic providers and downstream typed consumers.
Every former Box obligation is constructed from proofs. Only genuine general
published inputs, RH, and original downstream source inputs remain visible. -/
open Real
set_option maxHeartbeats 0

namespace RHSmoothingInputs.v2
/-- Canonical primary source uses integral0..x exactly as published; the
proved vanishing-on[0,1] identity is consumed in this actual source adapter. -/
theorem challenge_box_explicit_formula (hp : IntegratedPerron.v1.formula) :
    box_explicit_formula := by
  apply RHOcticPush.BoxPerron.box_explicit_formula_from_raw
  obtain ⟨C,hC⟩ := hp
  refine ⟨C,?_⟩
  intro x hx
  refine ⟨(hC x hx).1,?_⟩
  rw [RHOcticPush.BoxPerron.psi1_integral_from_zero]
  exact (hC x hx).2

theorem challenge_box_zero_estimate (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : box_zero_estimate :=
  RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hn hb
end RHSmoothingInputs.v2

namespace RHSmoothing.v3
theorem challenge_box_psi (rh : RH.v1.hypothesis)
    (he : RHSmoothingInputs.v2.box_explicit_formula)
    (hz : RHSmoothingInputs.v2.box_zero_estimate)
    (hm0 : BoxMellinInputs.v2.first_moment)
    (hm1 : BoxMellinInputs.v2.second_moment_identity) : box_psi :=
  RHOcticPush.BoxTail.actual_psi_improved rh he hz hm0 hm1

theorem challenge_box_gain : box_gain := RHOcticPush.BoxTail.envelope_gain
end RHSmoothing.v3

namespace Lcm.v6
theorem challenge_box_growth (hp : RHSmoothing.v3.box_psi) : box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hp (n:ℝ) hn
end Lcm.v6

namespace RHPrimeCounting.v4
theorem challenge_box_Li (ht : RHPrimeCounting.v3.refined_transfer)
    (hp : RHSmoothing.v3.box_psi) : box_Li :=
  RHPrimeCounting.v3.challenge_box_Li ht hp

theorem challenge_box_interval (hp : box_Li) : box_interval :=
  RHPrimeCounting.v3.challenge_box_interval hp
end RHPrimeCounting.v4

namespace Primorial.v4
theorem challenge_box_growth (rh : RH.v1.hypothesis) (hb : Buthe2016.v1.theorem_2_psi)
    (hp : RHSmoothing.v3.box_psi) : box_growth :=
  Primorial.v3.challenge_box_growth rh hb hp
end Primorial.v4

namespace RHOcticPush.Network
/-- Actual complete provider assembly. None of the four old Box predicates is
assumed. The GENERAL unformalized literature inputs are explicit, including
Perron, Nicolas, BPT and the original GM/Büthe downstream sources. -/
theorem fully_derived_box_network (rh : RH.v1.hypothesis)
    (hPerron : IntegratedPerron.v1.formula)
    (hNicolas : Nicolas.v1.spectral_bound) (hBPT : BPTOffOrdinate.v1.bound)
    (hGM : RHPrimeCounting.v1.gm_source) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTheta : Buthe2016.v1.theorem_2_psi) :
    RHSmoothingInputs.v2.box_explicit_formula ∧ RHSmoothingInputs.v2.box_zero_estimate ∧
    BoxMellinInputs.v2.first_moment ∧ BoxMellinInputs.v2.second_moment_identity ∧
    RHSmoothing.v3.box_psi ∧ Lcm.v6.box_growth ∧ Primorial.v4.box_growth ∧
    RHPrimeCounting.v4.box_Li ∧ RHPrimeCounting.v4.box_interval := by
  have he := RHSmoothingInputs.v2.challenge_box_explicit_formula hPerron
  have hz := RHSmoothingInputs.v2.challenge_box_zero_estimate hNicolas hBPT
  have hm0 := BoxMellinInputs.v2.challenge_first_moment
  have hm1 := BoxMellinInputs.v2.challenge_second_moment_identity
  have hp := RHSmoothing.v3.challenge_box_psi rh he hz hm0 hm1
  have ht := RHPrimeCounting.v3.challenge_refined_transfer rh hGM hP hJ
  have hpi := RHPrimeCounting.v4.challenge_box_Li ht hp
  exact ⟨he,hz,hm0,hm1,hp,Lcm.v6.challenge_box_growth hp,
    Primorial.v4.challenge_box_growth rh hTheta hp,hpi,
    RHPrimeCounting.v4.challenge_box_interval hpi⟩
end RHOcticPush.Network

#print axioms RHSmoothingInputs.v2.challenge_box_explicit_formula
#print axioms RHSmoothingInputs.v2.challenge_box_zero_estimate
#print axioms RHSmoothing.v3.challenge_box_psi
#print axioms RHSmoothing.v3.challenge_box_gain
#print axioms Lcm.v6.challenge_box_growth
#print axioms RHPrimeCounting.v4.challenge_box_Li
#print axioms RHPrimeCounting.v4.challenge_box_interval
#print axioms Primorial.v4.challenge_box_growth
#print axioms RHOcticPush.Network.fully_derived_box_network
