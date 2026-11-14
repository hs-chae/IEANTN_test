/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact44Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,2,1⟩,
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,507,2000⟩,
  ⟨3,0,2,0,0⟩,
  ⟨2,1,3,0,0⟩,
  ⟨3,0,4,0,0⟩,
  ⟨8,0,0,0,0⟩,
  ⟨3,0,6,0,0⟩,
  ⟨2,1,2,0,0⟩,
  ⟨3,7,8,0,0⟩,
  ⟨2,5,9,0,0⟩,
  ⟨7,0,0,0,0⟩,
  ⟨5,11,0,0,0⟩,
  ⟨3,10,12,0,0⟩,
  ⟨3,6,12,0,0⟩,
  ⟨0,0,0,227,1⟩,
  ⟨7,15,0,0,0⟩,
  ⟨0,0,0,675,1⟩,
  ⟨7,17,0,0,0⟩,
  ⟨2,16,18,0,0⟩,
  ⟨0,0,0,1000000000,1⟩,
  ⟨7,20,0,0,0⟩,
  ⟨3,8,21,0,0⟩,
  ⟨3,2,21,0,0⟩,
  ⟨6,23,0,0,0⟩,
  ⟨3,2,24,0,0⟩,
  ⟨5,25,0,0,0⟩,
  ⟨3,22,26,0,0⟩,
  ⟨5,23,0,0,0⟩,
  ⟨2,1,28,0,0⟩,
  ⟨5,21,0,0,0⟩,
  ⟨2,29,30,0,0⟩,
  ⟨0,0,0,7,1⟩,
  ⟨3,32,2,0,0⟩,
  ⟨0,0,0,12,1⟩,
  ⟨3,34,8,0,0⟩,
  ⟨3,35,20,0,0⟩,
  ⟨3,36,21,0,0⟩,
  ⟨5,37,0,0,0⟩,
  ⟨3,33,38,0,0⟩,
  ⟨2,31,39,0,0⟩,
  ⟨3,27,40,0,0⟩,
  ⟨3,41,41,0,0⟩,
  ⟨4,42,0,0,0⟩,
  ⟨2,1,43,0,0⟩,
  ⟨7,44,0,0,0⟩,
  ⟨3,0,45,0,0⟩,
  ⟨4,46,0,0,0⟩,
  ⟨2,19,47,0,0⟩,
  ⟨3,14,48,0,0⟩,
  ⟨2,49,6,0,0⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨7,51,0,0,0⟩,
  ⟨5,52,0,0,0⟩,
  ⟨3,50,53,0,0⟩,
  ⟨2,13,54,0,0⟩
]

def bound : Rat := mkRat (20) 1
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 56 := by decide +kernel
end ScopedNumerical.InputData.Fact44Row0
