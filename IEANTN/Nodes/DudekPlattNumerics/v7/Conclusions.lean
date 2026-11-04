/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
/-! Source-correct asymmetric historical input for the controlled forward numerical experiment. -/
namespace DudekPlattNumerics.v7
open Real IEANTN DudekPlatt.v3
/-- PNT+ Ramanujan.lean at c39a751, pi_lower_specific/pi_upper_specific and literal bounds.
The lower estimate starts at exp3914; the upper starts at exp3915. This is an explicit
historical source premise, not a replay of the larger PNT+ proof closure. -/
def pi_asymmetric_pnt : Prop :=
  (∀ x>exp 3914,mainTerm x-1194*(x/log x^6)<primeCounting x) ∧
  (∀ x>exp 3915,primeCounting x<mainTerm x+1426*(x/log x^6))
end DudekPlattNumerics.v7
