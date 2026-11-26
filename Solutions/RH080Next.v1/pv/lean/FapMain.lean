/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScalarHost
import FapActualF0
import FapActualArea
import FapActualHeight
import FapActualV0
import FapActualV1
import FapActualMu2
import FapActualMaximum
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FapPV
open ScalarHost

theorem actual_main_shape (run : String → Option Nat) :
    mainOutput program run = callSequence run ["f0_numerator", "positive_area_numerator", "component_height_numerator", "first_variation_numerator", "derivative_variation_numerator", "second_moment_numerator", "maximum_numerator"] := by rfl

theorem actual_main_output : mainOutput program (fun f => Execution.call 10000 f []) =
    some [799999999999990000, 16297236881532502, 1142770022680000, 14047086942420000, 40617111385600000, 760944122290429, 6915614327570000] := by
  rw [actual_main_shape]
  simp only [callSequence, Execution.actual_f0_numerator, Execution.actual_positive_area_numerator, Execution.actual_component_height, Execution.actual_first_variation_numerator, Execution.actual_derivative_variation_numerator, Execution.actual_second_moment_numerator, Execution.actual_maximum_numerator,
    Option.bind_some]
  rfl

#print axioms actual_main_output
end RH080Next.FapPV
