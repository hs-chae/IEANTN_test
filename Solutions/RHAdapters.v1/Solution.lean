/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Bridges.RH.LogicalAdapters

/-! Implement the exact generated challenges for the logical implication conclusions.
There is intentionally no theorem `RH.v1.challenge_hypothesis`.
-/
namespace RHAdapters.v1

theorem challenge_half_planes (rh_v1_hypothesis : RH.v1.hypothesis) :
    RHAdapters.v1.half_planes := RH.LogicalAdapters.half_planes rh_v1_hypothesis

theorem challenge_finite_heights (rh_v1_hypothesis : RH.v1.hypothesis) :
    RHAdapters.v1.finite_heights := RH.LogicalAdapters.finite_heights rh_v1_hypothesis

end RHAdapters.v1
