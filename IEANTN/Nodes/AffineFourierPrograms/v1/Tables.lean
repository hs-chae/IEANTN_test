/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Data.Rat.Defs

/-! Exact mathematical inputs of the two distinct C program instances. Values
are input coefficients, never asserted numerical outputs. Their correspondence
to actual C data and formal source models is proved in the separate Solutions. -/
namespace AffineFourierPrograms.v1

def sparseNumerators : List ℕ := [546871713113309800,546871713113309600,
  546871713113309600,546871713113309600,546871713113309600,
  546871713113309600,515419762691595100,357059942573668200,
  119725872611533800,0,0,0,0,0,0,0]
def flatNumerators : List ℕ := List.replicate 8 533333333333333333++List.replicate 8 0

def sparseNodes : List ℚ :=
  sparseNumerators.map (fun a : ℕ => (a : ℚ)/1000000000000000000)++[0]
def flatNodes : List ℚ :=
  flatNumerators.map (fun a : ℕ => (a : ℚ)/1000000000000000000)++[0]
end AffineFourierPrograms.v1
