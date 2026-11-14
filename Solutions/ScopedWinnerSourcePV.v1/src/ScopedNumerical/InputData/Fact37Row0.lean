/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedNumerical.Input
import LeanCert.Engine.IntervalEvalDyadic

namespace ScopedNumerical.InputData.Fact37Row0
open ScopedNumerical.Input
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def nodes : List Node := [
  ⟨0,0,0,601,625⟩,
  ⟨0,0,0,601,2500⟩,
  ⟨0,0,0,1,1⟩,
  ⟨0,0,0,3599,10000⟩,
  ⟨0,0,0,3000000000000,1⟩,
  ⟨0,0,0,2,1⟩,
  ⟨6,5,0,0,0⟩,
  ⟨3,4,6,0,0⟩,
  ⟨7,7,0,0,0⟩,
  ⟨5,8,0,0,0⟩,
  ⟨3,3,9,0,0⟩,
  ⟨2,2,10,0,0⟩,
  ⟨5,7,0,0,0⟩,
  ⟨3,11,12,0,0⟩,
  ⟨3,13,13,0,0⟩,
  ⟨3,1,14,0,0⟩,
  ⟨6,15,0,0,0⟩,
  ⟨3,0,16,0,0⟩,
  ⟨8,0,0,0,0⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,6,5⟩,
  ⟨7,20,0,0,0⟩,
  ⟨5,5,0,0,0⟩,
  ⟨3,21,22,0,0⟩,
  ⟨6,23,0,0,0⟩,
  ⟨3,19,24,0,0⟩,
  ⟨2,2,25,0,0⟩,
  ⟨7,26,0,0,0⟩,
  ⟨3,27,22,0,0⟩,
  ⟨6,28,0,0,0⟩,
  ⟨3,18,29,0,0⟩,
  ⟨0,0,0,529,1000⟩,
  ⟨3,30,31,0,0⟩,
  ⟨0,0,0,3599,5000⟩,
  ⟨5,33,0,0,0⟩,
  ⟨3,32,34,0,0⟩,
  ⟨3,33,9,0,0⟩,
  ⟨2,2,36,0,0⟩,
  ⟨3,37,37,0,0⟩,
  ⟨3,35,38,0,0⟩,
  ⟨0,0,0,1040111,2500000⟩,
  ⟨3,40,9,0,0⟩,
  ⟨6,41,0,0,0⟩,
  ⟨3,39,42,0,0⟩,
  ⟨0,0,0,3599,2000⟩,
  ⟨6,3,0,0,0⟩,
  ⟨3,44,45,0,0⟩,
  ⟨5,46,0,0,0⟩,
  ⟨3,31,47,0,0⟩,
  ⟨3,11,11,0,0⟩,
  ⟨3,48,49,0,0⟩,
  ⟨0,0,0,121,200⟩,
  ⟨0,0,0,-3599,5000⟩,
  ⟨6,52,0,0,0⟩,
  ⟨3,51,53,0,0⟩,
  ⟨3,8,8,0,0⟩,
  ⟨5,55,0,0,0⟩,
  ⟨3,54,56,0,0⟩,
  ⟨2,50,57,0,0⟩,
  ⟨3,58,18,0,0⟩,
  ⟨3,59,29,0,0⟩,
  ⟨3,60,12,0,0⟩,
  ⟨2,43,61,0,0⟩,
  ⟨0,0,0,601,1250⟩,
  ⟨5,63,0,0,0⟩,
  ⟨3,62,64,0,0⟩,
  ⟨7,18,0,0,0⟩,
  ⟨3,66,22,0,0⟩,
  ⟨6,67,0,0,0⟩,
  ⟨3,58,68,0,0⟩,
  ⟨7,1,0,0,0⟩,
  ⟨3,70,22,0,0⟩,
  ⟨6,71,0,0,0⟩,
  ⟨3,0,72,0,0⟩,
  ⟨5,73,0,0,0⟩,
  ⟨3,69,74,0,0⟩,
  ⟨2,65,75,0,0⟩,
  ⟨3,17,76,0,0⟩
]

def bound : Rat := mkRat (72089) 10000
def cfg : LeanCert.Engine.DyadicConfig := { precision := -100, taylorDepth := 32 }
def cells : Nat := 1
theorem wellFormed_nodes : wellFormed nodes = true := by decide +kernel
theorem node_count : nodes.length = 78 := by decide +kernel
end ScopedNumerical.InputData.Fact37Row0
