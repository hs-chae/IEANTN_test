/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHPrimeCounting.v5.Conclusions

/-! Actual one-pass prime-square feedback. All full lower-scale J terms,
prime-power allowances and the Li-from2 offset are retained. The minimum is
used only from log-height70, so the complete original35-ray is preserved. -/
namespace RHPrimeCounting.v6
open Real IEANTN
noncomputable def Jupper (L : ℝ) : ℝ :=
  IEANTN.li (exp L)+exp (L/2)/L*RHOcticEvolution.boxBound L+v5.profile L
noncomputable def rawRemainder (L : ℝ) : ℝ :=
  Jupper (L/2)/2+exp (L/4)/2+exp (L/3)*log (L/log 2)
noncomputable def effectiveRemainder (L : ℝ) : ℝ :=
  if 70 ≤ L then min (v3.primePowerRemainder L) (rawRemainder L)
  else v3.primePowerRemainder L
noncomputable def piEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L/2)/L*f L+v5.profile L+effectiveRemainder L+2
noncomputable def rawEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L/2)/L*f L+v5.profile L+rawRemainder L+2
/-- Actual J bound is obtained before ordinary-pi feedback, without a circular
ordinary-pi error assumption. The four earlier source inputs remain explicit. -/
def J_upper : Prop := ∀ L : ℝ, 35 ≤ L → riemannPrimeCounting (exp L) ≤ Jupper L
/-- The actual prime-power observable, using the complete lower-scale J bound. -/
def prime_power_feedback : Prop := ∀ L : ℝ, 35 ≤ L →
  riemannPrimeCounting (exp L)-primeCounting (exp L) ≤ effectiveRemainder L
/-- Typed psi and compensated-J providers transfer into actual ordinary pi. -/
def ordinary_transfer : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 35 ≤ L →
  |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L)*f L →
  |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ piEnvelope f L
/-- Complete Box envelope, for every real log-height at least35. -/
def box_Li : Prop := ∀ L : ℝ, 35 ≤ L →
  |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ piEnvelope RHOcticEvolution.boxBound L
/-- Actual count difference with both full feedback endpoint errors. -/
def box_interval : Prop := ∀ A B : ℝ, 35 ≤ A → A ≤ B →
  IEANTN.Li (exp B)-IEANTN.Li (exp A)-piEnvelope RHOcticEvolution.boxBound A-
    piEnvelope RHOcticEvolution.boxBound B ≤ primeCounting (exp B)-primeCounting (exp A)
/-- No loss anywhere on the complete old35-ray, including its clipped function. -/
def preserves_v5 : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 35 ≤ L →
  piEnvelope f L ≤ v5.effectiveEnvelope f L
/-- Exact formula identity before feedback becomes admissible. -/
def below70 : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), L < 70 →
  piEnvelope f L=v5.piEnvelope f L
/-- Above70 the entire lower-scale J function is used through the exact minimum. -/
def full_min : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 70 ≤ L →
  piEnvelope f L=min (v5.piEnvelope f L) (rawEnvelope f L)
/-- Strict quantified gain in the entire ordinary-pi function, not just a coefficient. -/
def whole_gain : Prop := ∀ (f : ℝ → ℝ) (L : ℝ), 100 ≤ L →
  (167/100 : ℝ)*exp (L/2)/L < v5.piEnvelope f L-piEnvelope f L
/-- Convenient strict scalar corollary, retaining Li as the integral from2. -/
def clean_pi : Prop := ∀ x : ℝ, exp 100 ≤ x →
  |primeCounting x-IEANTN.Li x| < sqrt x*(log x/(8*Real.pi)-(21/50))
/-- Exact .02sqrt(x) improvement over the preceding .4 scalar function. -/
def clean_gain : Prop := ∀ x : ℝ,
  sqrt x*(log x/(8*Real.pi)-(2/5))-sqrt x*(log x/(8*Real.pi)-(21/50))=sqrt x/50
end RHPrimeCounting.v6
