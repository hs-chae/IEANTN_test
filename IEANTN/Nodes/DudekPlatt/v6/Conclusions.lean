/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace DudekPlatt.v6
open Real IEANTN

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def ramanujan_145 : Prop :=
  ∀ x : ℝ, exp 145 < x →
    primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1)

end DudekPlatt.v6
