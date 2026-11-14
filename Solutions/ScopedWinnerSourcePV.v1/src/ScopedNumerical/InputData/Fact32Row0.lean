/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact32Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,281,100⟩,
  ⟨0,0,0,611,1000⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨0,0,0,1,1⟩,
  ⟨6,3,0,0,0⟩,
  ⟨3,2,4,0,0⟩,
  ⟨7,5,0,0,0⟩,
  ⟨0,0,0,6,1⟩,
  ⟨5,7,0,0,0⟩,
  ⟨3,6,8,0,0⟩,
  ⟨6,9,0,0,0⟩,
  ⟨3,1,10,0,0⟩,
  ⟨3,11,6,0,0⟩,
  ⟨5,12,0,0,0⟩,
  ⟨3,0,13,0,0⟩
]

def bound : Rat := mkRat (109037) 100000000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 15 := by decide +kernel
end ScopedNumerical.InputData.Fact32Row0
