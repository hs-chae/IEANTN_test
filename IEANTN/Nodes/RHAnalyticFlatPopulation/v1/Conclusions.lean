/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional
noncomputable section
open Real Filter IEANTN.CMSFunctional
open scoped Topology
namespace RHAnalyticFlatPopulation.v1

def familyWidth (m : ℕ) (α : ℝ) : ℝ :=
  (2*(m:ℝ)/(2*(m:ℝ)-1))*(α+(1+log (4*(m:ℝ)-2))/Real.pi)
def flat64Width (α : ℝ) : ℝ :=21/10+(128/127)*α

/-- Pure kernel analytic family. Every positive epsilon is retained; endpoint
GoodCoefficient membership is not inferred from the norm upper bound. -/
def family_curve : Prop := ∀m:ℕ,0<m→∀α:ℝ,0≤α→∀ε:ℝ,0<ε→
  GoodCoefficient α (familyWidth m α+ε)
/-- Nonempty actual good-coefficient set and infimum bound; no unsupported
endpoint attainment is asserted. -/
def family_infimum : Prop := ∀m:ℕ,0<m→∀α:ℝ,0≤α→
  (goodCoefficients α).Nonempty ∧ sInf (goodCoefficients α)≤familyWidth m α
/-- Fixed64 attained strict population curve, obtained with proved analytic
slack. This is kernel-only analytic, not source-first PV. -/
def flat64_curve : Prop := ∀α:ℝ,0≤α→GoodCoefficient α (flat64Width α)
/-- Actual forty-sqrt(x) eventual population coefficient; no finite onset. -/
def forty_population : Prop := GoodCoefficient 40 ((53867:ℝ)/1270)

/-- Deterministic real-density mesh; its totalized values away from the
positive eventual domain are not used in the asymptotic population proof. -/
def adaptiveMesh (α : ℝ) : ℕ :=⌊(Real.pi/2)*α⌋₊+1
def asymptoticConstant : ℝ :=(2+log (2*Real.pi))/Real.pi
/-- Unconditional real-alpha analytic limit. No source, RH or numerical
input is needed, and no optimality statement is made. -/
def adaptive_limit : Prop :=
  Tendsto (fun α : ℝ=>familyWidth (adaptiveMesh α) α-α-log α/Real.pi)
    atTop (𝓝 asymptoticConstant)
/-- Density first, then prime-variable onset: every eta>0 eventually in real
alpha gives a strict positive eventual prime-population margin. This does not
assert a jointly uniform onset in alpha and x. Pure analytic, not PV. -/
def adaptive_population : Prop :=∀η:ℝ,0<η→∀ᶠα:ℝ in atTop,
  GoodCoefficient α (α+log α/Real.pi+asymptoticConstant+η)

end RHAnalyticFlatPopulation.v1
