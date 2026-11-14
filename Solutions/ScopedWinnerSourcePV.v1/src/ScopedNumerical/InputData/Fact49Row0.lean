/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact49Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,601,5000⟩,
  ⟨0,0,0,2,1⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨3,2,2,0,0⟩,
  ⟨3,1,3,0,0⟩,
  ⟨5,4,0,0,0⟩,
  ⟨3,0,5,0,0⟩,
  ⟨6,6,0,0,0⟩
]

def bound : Rat := mkRat (1000000000001) 1000000000000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 8 := by decide +kernel
end ScopedNumerical.InputData.Fact49Row0
