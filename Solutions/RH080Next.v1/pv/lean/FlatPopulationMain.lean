/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScalarHost
import FlatPopulationActual
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FlatPopulationPV
open ScalarHost

theorem actual_main_shape (run : String → Option Nat) :
    mainOutput program run = callSequence run ["population_norm_upper"] := by rfl

theorem actual_main_output : mainOutput program (fun f => Execution.call 10000 f []) =
    some [1120475208606944546] := by
  rw [actual_main_shape]
  simp only [callSequence, Execution.actual_norm_program,
    Option.bind_some]
  rfl

#print axioms actual_main_output
end RH080Next.FlatPopulationPV
