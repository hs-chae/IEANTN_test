/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary
namespace FKS2.v4
open Real IEANTN
noncomputable def Uold : ℝ := 121.096 * (1+(11:ℝ)/10^62)
def baseline_theta : Prop := HasClassicalBound Eθ Uold (3/2) 2 5.5666305 (exp 300)
def baseline_intervals : Prop := ∀ x ≥ exp 300, HasPrimeInInterval x (x/16)
end FKS2.v4
