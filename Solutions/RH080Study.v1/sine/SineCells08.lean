/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SineSpec
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080.SineBridge
theorem error128 : |(sineFixed 128 : ℚ)/1000000000 - polyQ ((3141592654*128/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]
end RH080.SineBridge
