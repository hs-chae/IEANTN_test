/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact18Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,3000000000000,1⟩,
  ⟨0,0,0,4,1⟩,
  ⟨6,1,0,0,0⟩,
  ⟨3,0,2,0,0⟩,
  ⟨7,3,0,0,0⟩
]

def bound : Rat := mkRat (32729633) 1000000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 5 := by decide +kernel
end ScopedNumerical.InputData.Fact18Row0
