/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScalarHost
import WindowActualF0
import WindowActualArea
import WindowActualHeight
import WindowActualV0
import WindowActualV1
import WindowActualMu2
import WindowActualMaximum
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.WindowPV
open ScalarHost

theorem actual_main_shape (run : String → Option Nat) :
    mainOutput program run = callSequence run ["f0_numerator", "positive_area_numerator", "component_height_numerator", "first_variation_numerator", "derivative_variation_numerator", "second_moment_numerator", "maximum_numerator"] := by rfl

theorem actual_main_output : mainOutput program (fun f => Execution.call 10000 f []) =
    some [3599999999999999998, 73712934591273687, 1146154494119977, 14033179036371096, 40713308729275680, 69452659995205718, 6911696218056550] := by
  rw [actual_main_shape]
  simp only [callSequence, Execution.actual_f0_numerator, Execution.actual_positive_area_numerator, Execution.actual_component_height, Execution.actual_first_variation_numerator, Execution.actual_derivative_variation_numerator, Execution.actual_second_moment_numerator, Execution.actual_maximum_numerator,
    Option.bind_some]
  rfl

#print axioms actual_main_output
end RH080Next.WindowPV
