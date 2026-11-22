/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import StieltjesTrapezoid
import CLogMomentNetwork

/-! The actual source-linked box PNT consumer loses its Stieltjes hypothesis.
The C execution/aggregation proof is reused unchanged; the new sequence theorem
is ordinary kernel analysis. Four analytic inputs and RH remain explicit. -/
namespace RHLimit.BoxMomentReduced

theorem box_moments
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity) :
    RHSmoothingInputs.v1.box_moments :=
  RHContinuation.CLogMomentNetwork.box_moments hfirst hsecond
    RHLimit.Stieltjes.stieltjes_trapezoid

theorem box_psi (rh : RiemannHypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity) :
    RHSmoothing.v1.box_psi :=
  RHContinuation.CLogMomentNetwork.box_psi rh hef hz hfirst hsecond
    RHLimit.Stieltjes.stieltjes_trapezoid

#print axioms box_moments
#print axioms box_psi
#check @box_psi
end RHLimit.BoxMomentReduced
