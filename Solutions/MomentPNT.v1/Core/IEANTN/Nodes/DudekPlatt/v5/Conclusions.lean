/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A stronger threshold than the pre-experiment network; no best-known claim is made. -/
namespace DudekPlatt.v5
open Real IEANTN

/-- The literal Ramanujan inequality for every real x>e^401. -/
def ramanujan_401 : Prop := ∀ x : ℝ, exp 401 < x →
  primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1)

end DudekPlatt.v5
