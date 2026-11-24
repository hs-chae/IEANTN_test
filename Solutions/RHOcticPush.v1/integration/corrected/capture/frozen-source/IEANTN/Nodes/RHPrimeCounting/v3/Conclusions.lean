/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOcticEvolution
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Nodes.RHSmoothing.v1.Conclusions

/-! Evolved whole functions for actual ordinary prime counting, with explicit
prime-power and offset-Li2 corrections and a correlated two-height contract. -/
namespace RHPrimeCounting.v3
open Real IEANTN
noncomputable def leading (b x : ℝ) : ℝ :=
  (693 / 5000 : ℝ) * sqrt x / (log x * (log x - b))
noncomputable def oldCorrection (x : ℝ) : ℝ := 361 / 25 + leading 6 x
noncomputable def evolvedCorrection (x : ℝ) : ℝ :=
  if exp 15 ≤ x then min (oldCorrection x) ((1551 / 100 : ℝ) + leading 5 x)
  else oldCorrection x
noncomputable def primitiveEnvelope (x : ℝ) : ℝ :=
  (231 / 5000 : ℝ) * x * sqrt x + (919 / 500 : ℝ) * x + 19851 / 10000 +
    (5097 / 10000 : ℝ) / x
noncomputable def weight (x : ℝ) : ℝ := 1 / (x * (log x) ^ 2)
noncomputable def error (x : ℝ) : ℝ :=
  riemannPrimeCounting x - IEANTN.li x - (Chebyshev.psi x - x) / log x
noncomputable def pairBudget (K y x : ℝ) : ℝ :=
  K * (leading 5 x - leading 5 y + 2 * primitiveEnvelope y * weight y +
    (919 / 500 : ℝ) / log y) + (exp 1 - K) * ((1551 / 100 : ℝ) + leading 5 y)
noncomputable def primePowerRemainder (L : ℝ) : ℝ :=
  2 * log 4 * exp (L / 2) / L + exp (L / 4) / 2 +
    exp (L / 3) * log (L / log 2)
noncomputable def piEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  exp (L / 2) / L * f L + evolvedCorrection (exp L) + primePowerRemainder L + 2
/-- Actual compensated Riemann prime-counting error, same GM/Büthe source inputs. -/
def refined_transfer : Prop := ∀ x : ℝ, exp 12 ≤ x → |error x| ≤ evolvedCorrection x
/-- Complete old function is retained; strict gain is stated only on its proved late ray. -/
def transfer_gain : Prop :=
  (∀ x : ℝ, evolvedCorrection x ≤ oldCorrection x) ∧
  ∀ x : ℝ, exp 24 ≤ x → (1 / 2 : ℝ) < oldCorrection x - evolvedCorrection x
/-- Shared-prefix cancellation before absolute values, with every coefficient guard. -/
def paired_transfer : Prop := ∀ K y x : ℝ, 0 ≤ K → K ≤ exp 1 →
  exp 15 ≤ y → y ≤ x → K * error x - exp 1 * error y ≤ pairBudget K y x
/-- Actual ordinary pi and offset Li2 with the improved box and GM functions. -/
def box_Li : Prop := ∀ L : ℝ, 35 ≤ L →
  |primeCounting (exp L) - IEANTN.Li (exp L)| ≤ piEnvelope RHOcticEvolution.boxBound L
/-- Same GM improvement with the independent previously proved CH psi provider. -/
def ch_Li : Prop := ∀ L : ℝ, 34 ≤ L →
  |primeCounting (exp L) - IEANTN.Li (exp L)| ≤ piEnvelope RHSmoothing.chBound L
/-- Actual count in (exp A,exp B], preserving both complete endpoint envelopes. -/
def box_interval : Prop := ∀ A B : ℝ, 35 ≤ A → A ≤ B →
  IEANTN.Li (exp B) - IEANTN.Li (exp A) -
      piEnvelope RHOcticEvolution.boxBound A - piEnvelope RHOcticEvolution.boxBound B ≤
    primeCounting (exp B) - primeCounting (exp A)
end RHPrimeCounting.v3
