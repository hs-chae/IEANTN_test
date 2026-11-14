/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact30Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,611,1000⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨0,0,0,4,1⟩,
  ⟨6,2,0,0,0⟩,
  ⟨3,1,3,0,0⟩,
  ⟨7,4,0,0,0⟩,
  ⟨0,0,0,6,1⟩,
  ⟨5,6,0,0,0⟩,
  ⟨3,5,7,0,0⟩,
  ⟨6,8,0,0,0⟩,
  ⟨3,0,9,0,0⟩,
  ⟨3,10,5,0,0⟩,
  ⟨7,5,0,0,0⟩,
  ⟨0,0,0,2,1⟩,
  ⟨5,13,0,0,0⟩,
  ⟨3,12,14,0,0⟩,
  ⟨6,15,0,0,0⟩,
  ⟨3,11,16,0,0⟩,
  ⟨5,17,0,0,0⟩
]

def bound : Rat := mkRat (3737) 100000000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 19 := by decide +kernel
end ScopedNumerical.InputData.Fact30Row0
