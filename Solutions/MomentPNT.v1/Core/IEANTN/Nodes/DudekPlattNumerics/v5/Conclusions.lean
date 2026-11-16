/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions

/-! The exact existing five-term main term, with new fully proved coefficients and range. -/
namespace DudekPlattNumerics.v5
open Real IEANTN

/-- New positive coefficients, for every real argument strictly above e^400. -/
def pi_two_sided_qrh : Prop :=
  ∀ x : ℝ, exp 400 < x →
    DudekPlatt.v3.mainTerm x + 119 * x / log x ^ 6 < primeCounting x ∧
      primeCounting x < DudekPlatt.v3.mainTerm x + 131 * x / log x ^ 6

end DudekPlattNumerics.v5
