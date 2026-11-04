/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeCounting
/-! Preregistered historical-input forward numerical experiment. -/
namespace RamanujanGap.v1
open Real IEANTN
/-- The actual Ramanujan expression; shared unchanged by later versions. -/
noncomputable def gap (x : ℝ) : ℝ :=
  exp 1*x/log x*primeCounting (x/exp 1)-primeCounting x^2
/-- Nonnegative normalized shortfall from its leading asymptotic gap. -/
noncomputable def loss (x : ℝ) : ℝ := max 0 (1-log x^6/x^2*gap x)
/-- Quantitative old numerical consequence on the same strict whole ray as the existing application. -/
def loss_bound : Prop := ∀ x>exp 3915,loss x≤3914.7/log x
/-- A lower bound on the actual prime-counting expression, not just on numerical parameters. -/
def gap_lower_bound : Prop := ∀ x>exp 3915,
  (1-3914.7/log x)*x^2/log x^6<gap x
/-- The existing Ramanujan inequality obtained through the new consumed numerical certificate. -/
def ramanujan : Prop := ∀ x>exp 3915,primeCounting x^2<exp 1*x/log x*primeCounting (x/exp 1)
end RamanujanGap.v1
