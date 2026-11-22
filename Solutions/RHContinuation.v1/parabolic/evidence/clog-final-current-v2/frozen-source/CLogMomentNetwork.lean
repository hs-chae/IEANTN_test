/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CLogMoment
import IEANTN.Nodes.BoxMellinInputs.v1.Conclusions
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions
import IEANTN.Nodes.RHSmoothing.v1.Conclusions

namespace RHContinuation.CLogMomentNetwork
/-- Source-first actual C log executions and kernel aggregation discharge the
existing network's numerical moment leaf, retaining three exact analytic inputs.
The binder order matches the canonical per-conclusion import list. -/
theorem box_moments
    (boxMellinInputs_v1_first_moment : BoxMellinInputs.v1.first_moment)
    (boxMellinInputs_v1_second_moment_identity : BoxMellinInputs.v1.second_moment_identity)
    (boxMellinInputs_v1_stieltjes_trapezoid : BoxMellinInputs.v1.stieltjes_trapezoid) :
    RHSmoothingInputs.v1.box_moments := by
  constructor
  · exact boxMellinInputs_v1_first_moment.2
  · have hs : CLogMoment.StieltjesTrapezoidLower :=
      boxMellinInputs_v1_stieltjes_trapezoid.2
    have hm : CLogMoment.MellinMomentIdentity :=
      boxMellinInputs_v1_second_moment_identity.2
    exact (CLogMoment.source_moment_bound_closed hs hm).le

/-- Full source-linked actual network PNT consumer. There is no numerical-moment
premise: those are supplied by the actual C execution and kernel aggregation. -/
theorem box_psi (rh : RiemannHypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (boxMellinInputs_v1_first_moment : BoxMellinInputs.v1.first_moment)
    (boxMellinInputs_v1_second_moment_identity : BoxMellinInputs.v1.second_moment_identity)
    (boxMellinInputs_v1_stieltjes_trapezoid : BoxMellinInputs.v1.stieltjes_trapezoid) :
    RHSmoothing.v1.box_psi := by
  have hm := box_moments boxMellinInputs_v1_first_moment
    boxMellinInputs_v1_second_moment_identity boxMellinInputs_v1_stieltjes_trapezoid
  exact RHContinuation.Parabolic.psi_fast rh hef hz hm.1 hm.2

#print axioms box_moments
#print axioms box_psi
#print box_psi
end RHContinuation.CLogMomentNetwork
