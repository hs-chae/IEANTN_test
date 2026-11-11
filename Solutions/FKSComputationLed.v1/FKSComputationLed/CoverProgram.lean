/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.Input
namespace FKSComputationLed.CoverProgram
open Input
instance : Inhabited Cell := ⟨⟨0,0,0,0⟩⟩
def lower : Nat := 100000000
def upper : Nat := 1000000000
def shapeAux (U : Nat) : Nat → List Cell → Bool
  | p, [] => decide (p=U)
  | p, z::zs => decide (p=z.a ∧ z.a<z.b ∧ z.b≤U) && shapeAux U z.b zs
def geometryGate : Bool :=
  decide (0<Input.cells.size ∧ Input.cells[0]!.a=lower) &&
    shapeAux upper lower Input.cells.toList
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem geometry_checked : geometryGate=true := by native_decide
#print axioms geometry_checked
end FKSComputationLed.CoverProgram
