/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
namespace FKS2.v9
open Real IEANTN
def old_absolute_pi : Prop := ∀ x ≥ exp 330,
  |primeCounting x-Li x| ≤ (1.69e-12:ℝ)*(x/log x)
def qrh_absolute_pi : Prop := ∀ x ≥ exp 330,
  |primeCounting x-Li x| ≤ ((5:ℝ)/10^16)*(x/log x)
def paired_absolute_pi : Prop := old_absolute_pi ∧ qrh_absolute_pi
def strict_reconstructed_improvement : Prop := (5:ℝ)/10^16 < 1.69e-12
def strict_historical_improvement : Prop := (5:ℝ)/10^16 < 1.6855e-12
def exact_allowance_ratios : Prop :=
  (1.69e-12:ℝ)/((5:ℝ)/10^16)=3380 ∧
  (1.6855e-12:ℝ)/((5:ℝ)/10^16)=3371
end FKS2.v9
