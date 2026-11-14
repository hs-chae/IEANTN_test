/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact40Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,2,1⟩,
  ⟨0,0,0,18056,3167⟩,
  ⟨7,1,0,0,0⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,0,0,3599,2500⟩,
  ⟨0,0,0,4,3⟩,
  ⟨0,0,0,3167,18056⟩,
  ⟨0,0,0,-7349,3750⟩,
  ⟨6,7,0,0,0⟩,
  ⟨3,6,8,0,0⟩,
  ⟨2,5,9,0,0⟩,
  ⟨3,4,10,0,0⟩,
  ⟨2,3,11,0,0⟩
]

def bound : Rat := mkRat (54281) 10000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 13 := by decide +kernel
end ScopedNumerical.InputData.Fact40Row0
