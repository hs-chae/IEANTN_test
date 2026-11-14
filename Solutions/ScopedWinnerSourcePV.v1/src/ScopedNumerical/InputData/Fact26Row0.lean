/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact26Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨8,0,0,0,0⟩,
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,6,5⟩,
  ⟨7,3,0,0,0⟩,
  ⟨0,0,0,2,1⟩,
  ⟨5,5,0,0,0⟩,
  ⟨3,4,6,0,0⟩,
  ⟨6,7,0,0,0⟩,
  ⟨3,2,8,0,0⟩,
  ⟨2,1,9,0,0⟩,
  ⟨7,10,0,0,0⟩,
  ⟨3,11,6,0,0⟩,
  ⟨6,12,0,0,0⟩,
  ⟨3,0,13,0,0⟩,
  ⟨0,0,0,31,50⟩,
  ⟨3,14,15,0,0⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨0,0,0,4,1⟩,
  ⟨6,18,0,0,0⟩,
  ⟨3,17,19,0,0⟩,
  ⟨7,20,0,0,0⟩,
  ⟨5,21,0,0,0⟩,
  ⟨3,16,22,0,0⟩,
  ⟨0,0,0,6,1⟩,
  ⟨3,24,13,0,0⟩,
  ⟨3,0,20,0,0⟩,
  ⟨5,26,0,0,0⟩,
  ⟨3,25,27,0,0⟩,
  ⟨2,23,28,0,0⟩,
  ⟨0,0,0,131,125⟩,
  ⟨3,14,30,0,0⟩,
  ⟨3,20,21,0,0⟩,
  ⟨5,32,0,0,0⟩,
  ⟨3,31,33,0,0⟩,
  ⟨2,29,34,0,0⟩
]

def bound : Rat := mkRat (39141) 500000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 36 := by decide +kernel
end ScopedNumerical.InputData.Fact26Row0
