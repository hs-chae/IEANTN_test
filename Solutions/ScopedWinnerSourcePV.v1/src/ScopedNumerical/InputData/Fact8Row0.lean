/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact8Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,3,16384⟩,
  ⟨0,0,0,2,1⟩,
  ⟨0,0,0,0,1⟩,
  ⟨1,0,0,0,0⟩,
  ⟨3,0,3,0,0⟩,
  ⟨2,2,4,0,0⟩,
  ⟨2,5,0,0,0⟩,
  ⟨3,1,6,0,0⟩,
  ⟨0,0,0,601,2500⟩,
  ⟨3,1,5,0,0⟩,
  ⟨6,9,0,0,0⟩,
  ⟨3,8,10,0,0⟩,
  ⟨4,11,0,0,0⟩,
  ⟨2,7,12,0,0⟩,
  ⟨6,13,0,0,0⟩,
  ⟨0,0,0,642031,1000000⟩,
  ⟨6,6,0,0,0⟩,
  ⟨3,15,16,0,0⟩,
  ⟨0,0,0,83377,1000000⟩,
  ⟨2,17,18,0,0⟩,
  ⟨7,19,0,0,0⟩,
  ⟨5,1,0,0,0⟩,
  ⟨3,20,21,0,0⟩,
  ⟨6,22,0,0,0⟩,
  ⟨0,0,0,6,1⟩,
  ⟨5,24,0,0,0⟩,
  ⟨3,6,25,0,0⟩,
  ⟨6,26,0,0,0⟩,
  ⟨0,0,0,1,1⟩,
  ⟨3,28,6,0,0⟩,
  ⟨0,0,0,30729633,1000000⟩,
  ⟨5,30,0,0,0⟩,
  ⟨3,29,31,0,0⟩,
  ⟨2,28,32,0,0⟩,
  ⟨3,27,33,0,0⟩,
  ⟨0,0,0,17859,20000000⟩,
  ⟨2,34,35,0,0⟩,
  ⟨3,23,36,0,0⟩,
  ⟨0,0,0,5733,100000000⟩,
  ⟨3,6,21,0,0⟩,
  ⟨6,39,0,0,0⟩,
  ⟨3,38,40,0,0⟩,
  ⟨2,37,41,0,0⟩,
  ⟨3,42,42,0,0⟩,
  ⟨3,14,43,0,0⟩,
  ⟨3,0,44,0,0⟩
]

def bound : Rat := mkRat (3309471) 1000000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 24 }
def cells : Nat := 16384
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 46 := by decide +kernel
end ScopedNumerical.InputData.Fact8Row0
