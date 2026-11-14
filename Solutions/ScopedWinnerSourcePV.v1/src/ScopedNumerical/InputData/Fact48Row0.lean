/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact48Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,1237,1000⟩,
  ⟨4,0,0,0,0⟩,
  ⟨2,1,2,0,0⟩,
  ⟨2,0,3,0,0⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨7,5,0,0,0⟩,
  ⟨3,4,6,0,0⟩,
  ⟨3,3,6,0,0⟩,
  ⟨6,8,0,0,0⟩,
  ⟨3,3,9,0,0⟩,
  ⟨5,10,0,0,0⟩,
  ⟨3,7,11,0,0⟩,
  ⟨5,8,0,0,0⟩,
  ⟨2,0,13,0,0⟩,
  ⟨5,6,0,0,0⟩,
  ⟨2,14,15,0,0⟩,
  ⟨0,0,0,7,1⟩,
  ⟨3,17,3,0,0⟩,
  ⟨0,0,0,12,1⟩,
  ⟨3,19,4,0,0⟩,
  ⟨3,20,5,0,0⟩,
  ⟨3,21,6,0,0⟩,
  ⟨5,22,0,0,0⟩,
  ⟨3,18,23,0,0⟩,
  ⟨2,16,24,0,0⟩,
  ⟨3,12,25,0,0⟩
]

def bound : Rat := mkRat (1) 4
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 27 := by decide +kernel
end ScopedNumerical.InputData.Fact48Row0
