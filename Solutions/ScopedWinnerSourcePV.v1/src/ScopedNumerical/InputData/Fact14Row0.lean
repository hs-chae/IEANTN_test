/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact14Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,1,2⟩,
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨4,1,0,0,0⟩,
  ⟨2,2,3,0,0⟩,
  ⟨5,4,0,0,0⟩,
  ⟨4,5,0,0,0⟩,
  ⟨2,1,6,0,0⟩,
  ⟨3,7,7,0,0⟩,
  ⟨5,8,0,0,0⟩,
  ⟨3,0,9,0,0⟩,
  ⟨0,0,0,601,2500⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,12463,10000⟩,
  ⟨7,13,0,0,0⟩,
  ⟨3,12,14,0,0⟩,
  ⟨0,0,0,3,4⟩,
  ⟨0,0,0,71843,10000⟩,
  ⟨7,17,0,0,0⟩,
  ⟨3,16,18,0,0⟩,
  ⟨2,15,19,0,0⟩,
  ⟨2,11,20,0,0⟩,
  ⟨0,0,0,25521,20000⟩,
  ⟨0,0,0,4,3⟩,
  ⟨0,0,0,12463,71843⟩,
  ⟨0,0,0,-7349,3750⟩,
  ⟨6,25,0,0,0⟩,
  ⟨3,24,26,0,0⟩,
  ⟨2,23,27,0,0⟩,
  ⟨3,22,28,0,0⟩,
  ⟨2,21,29,0,0⟩,
  ⟨6,30,0,0,0⟩,
  ⟨3,10,31,0,0⟩,
  ⟨0,0,0,2,1⟩,
  ⟨8,0,0,0,0⟩,
  ⟨3,33,34,0,0⟩,
  ⟨0,0,0,3681,10000⟩,
  ⟨3,35,36,0,0⟩,
  ⟨5,37,0,0,0⟩,
  ⟨3,32,38,0,0⟩
]

def bound : Rat := mkRat (72091) 10000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 40 := by decide +kernel
end ScopedNumerical.InputData.Fact14Row0
