/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact46Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,507,2000⟩,
  ⟨2,0,1,0,0⟩,
  ⟨0,0,0,1000000000,1⟩,
  ⟨7,3,0,0,0⟩,
  ⟨3,2,4,0,0⟩,
  ⟨3,1,4,0,0⟩,
  ⟨6,6,0,0,0⟩,
  ⟨3,1,7,0,0⟩,
  ⟨5,8,0,0,0⟩,
  ⟨3,5,9,0,0⟩,
  ⟨5,6,0,0,0⟩,
  ⟨2,0,11,0,0⟩,
  ⟨5,4,0,0,0⟩,
  ⟨2,12,13,0,0⟩,
  ⟨0,0,0,7,1⟩,
  ⟨3,15,1,0,0⟩,
  ⟨0,0,0,12,1⟩,
  ⟨3,17,2,0,0⟩,
  ⟨3,18,3,0,0⟩,
  ⟨3,19,4,0,0⟩,
  ⟨5,20,0,0,0⟩,
  ⟨3,16,21,0,0⟩,
  ⟨2,14,22,0,0⟩,
  ⟨3,10,23,0,0⟩
]

def bound : Rat := mkRat (3) 4
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 25 := by decide +kernel
end ScopedNumerical.InputData.Fact46Row0
