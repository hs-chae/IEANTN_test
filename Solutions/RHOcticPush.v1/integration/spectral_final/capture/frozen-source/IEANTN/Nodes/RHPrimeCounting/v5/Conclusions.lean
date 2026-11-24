/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHPrimeCounting.v3.Conclusions

/-! Signed full-zero compensation and actual ordinary prime counting. The
whole old/new functions are compared on their common ray; general Perron and
Nicolas inputs remain explicit, and the previous GM/Büthe transfer assumptions
are absent from the new source provider. -/
namespace RHPrimeCounting.v5
open Real IEANTN
noncomputable def profile (L : ℝ) : ℝ :=
  (579/125 : ℝ)+(47/1000)*(1+4/(L-8))*(exp (L/2)/L^2)
noncomputable def piEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L/2)/L*f L+profile L+RHPrimeCounting.v3.primePowerRemainder L+2
noncomputable def effectiveEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  min (RHPrimeCounting.v3.piEnvelope f L) (piEnvelope f L)
/-- Full nonconstant bound for the actual compensated Riemann prime count. -/
def compensation_profile : Prop := ∀ x : ℝ, exp 24 ≤ x →
  |RHPrimeCounting.v3.error x| ≤ profile (log x)
/-- Requested strict coefficient, with full real-ray coverage from exp24. -/
def compensation_076 : Prop := ∀ x : ℝ, exp 24 ≤ x →
  |RHPrimeCounting.v3.error x| < (76/1000)*(sqrt x/(log x)^2)
/-- Stronger strict coefficient on the Box route's existing exp35 onset. -/
def compensation_055 : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |RHPrimeCounting.v3.error x| < (55/1000)*(sqrt x/(log x)^2)
/-- Whole ordinary-pi transfer, including actual prime powers and offsetLi2. -/
def ordinary_transfer : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 24 ≤ L →
  |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L)*f L →
  |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ piEnvelope f L
/-- Complete effective whole-function Box pi bound on its original real ray. -/
def box_Li : Prop := ∀ L : ℝ, 35 ≤ L →
  |primeCounting (exp L)-IEANTN.Li (exp L)| ≤
    effectiveEnvelope RHOcticEvolution.boxBound L
/-- Actual count difference with both complete improved endpoint errors. -/
def box_interval : Prop := ∀ A B : ℝ, 35 ≤ A → A ≤ B →
  IEANTN.Li (exp B)-IEANTN.Li (exp A)-effectiveEnvelope RHOcticEvolution.boxBound A-
    effectiveEnvelope RHOcticEvolution.boxBound B ≤ primeCounting (exp B)-primeCounting (exp A)
/-- The independent existing CH psi provider also receives the same signed
transfer, while retaining its earlier exp34 onset explicitly. -/
def ch_Li : Prop := ∀ L : ℝ, 34 ≤ L →
  |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ effectiveEnvelope RHSmoothing.chBound L
/-- Actual complete two-endpoint CH count, retaining its own onset. -/
def ch_interval : Prop := ∀ A B : ℝ, 34 ≤ A → A ≤ B →
  IEANTN.Li (exp B)-IEANTN.Li (exp A)-effectiveEnvelope RHSmoothing.chBound A-
    effectiveEnvelope RHSmoothing.chBound B ≤ primeCounting (exp B)-primeCounting (exp A)
/-- Quantified strict gain in the entire ordinary-pi envelope on every L>=24. -/
def whole_gain : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 24 ≤ L →
  (14:ℝ) < RHPrimeCounting.v3.piEnvelope f L-piEnvelope f L
/-- The clipped minimum equals the stronger function throughout its valid ray. -/
def effective_min : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 24 ≤ L →
  effectiveEnvelope f L=piEnvelope f L
end RHPrimeCounting.v5
