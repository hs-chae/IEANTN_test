/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions

namespace DudekPlattNumerics.v6
open Real IEANTN

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def pi_two_sided_144 : Prop :=
  ∀ x : ℝ, exp 144 < x →
    DudekPlatt.v3.mainTerm x + 70 * x / log x ^ 6 < primeCounting x ∧
    primeCounting x < DudekPlatt.v3.mainTerm x + 170 * x / log x ^ 6

end DudekPlattNumerics.v6
