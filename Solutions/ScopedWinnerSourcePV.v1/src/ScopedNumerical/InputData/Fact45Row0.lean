/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact45Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,2,1⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨7,1,0,0,0⟩,
  ⟨3,2,2,0,0⟩,
  ⟨3,0,3,0,0⟩,
  ⟨0,0,0,1237,1000⟩,
  ⟨3,0,5,0,0⟩,
  ⟨4,0,0,0,0⟩,
  ⟨2,6,7,0,0⟩,
  ⟨3,8,2,0,0⟩,
  ⟨6,9,0,0,0⟩,
  ⟨5,10,0,0,0⟩,
  ⟨3,4,11,0,0⟩,
  ⟨0,0,0,4,1⟩,
  ⟨3,13,5,0,0⟩,
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,3,1⟩,
  ⟨4,15,0,0,0⟩,
  ⟨2,6,17,0,0⟩,
  ⟨3,18,2,0,0⟩,
  ⟨5,19,0,0,0⟩,
  ⟨3,16,20,0,0⟩,
  ⟨2,15,21,0,0⟩,
  ⟨0,0,0,6,1⟩,
  ⟨3,19,19,0,0⟩,
  ⟨5,24,0,0,0⟩,
  ⟨3,23,25,0,0⟩,
  ⟨2,22,26,0,0⟩,
  ⟨3,24,19,0,0⟩,
  ⟨5,28,0,0,0⟩,
  ⟨3,23,29,0,0⟩,
  ⟨2,27,30,0,0⟩,
  ⟨3,14,31,0,0⟩,
  ⟨5,18,0,0,0⟩,
  ⟨3,32,33,0,0⟩,
  ⟨8,0,0,0,0⟩,
  ⟨3,0,35,0,0⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,6,5⟩,
  ⟨7,38,0,0,0⟩,
  ⟨5,0,0,0,0⟩,
  ⟨3,39,40,0,0⟩,
  ⟨6,41,0,0,0⟩,
  ⟨3,37,42,0,0⟩,
  ⟨2,15,43,0,0⟩,
  ⟨7,44,0,0,0⟩,
  ⟨3,45,40,0,0⟩,
  ⟨6,46,0,0,0⟩,
  ⟨3,36,47,0,0⟩,
  ⟨2,18,17,0,0⟩,
  ⟨3,49,2,0,0⟩,
  ⟨5,50,0,0,0⟩,
  ⟨3,16,51,0,0⟩,
  ⟨2,15,52,0,0⟩,
  ⟨3,50,50,0,0⟩,
  ⟨5,54,0,0,0⟩,
  ⟨3,23,55,0,0⟩,
  ⟨2,53,56,0,0⟩,
  ⟨3,54,50,0,0⟩,
  ⟨5,58,0,0,0⟩,
  ⟨3,23,59,0,0⟩,
  ⟨2,57,60,0,0⟩,
  ⟨3,18,61,0,0⟩,
  ⟨3,48,62,0,0⟩,
  ⟨2,5,17,0,0⟩,
  ⟨5,64,0,0,0⟩,
  ⟨3,63,65,0,0⟩,
  ⟨2,34,66,0,0⟩,
  ⟨3,12,67,0,0⟩
]

def bound : Rat := mkRat (1) 1
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 69 := by decide +kernel
end ScopedNumerical.InputData.Fact45Row0
