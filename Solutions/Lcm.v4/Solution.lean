/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NetworkConsumers

namespace Lcm.v4
open Real IEANTN
theorem challenge_box_growth (hi : RHSmoothing.v1.box_psi) : Lcm.v4.box_growth :=
  by apply RHContinuation.Network.box_lcm <;> assumption

#print axioms challenge_box_growth

theorem challenge_recovered_growth (hi : RHSmoothing.v1.recovered_ch_psi) : Lcm.v4.recovered_growth :=
  by apply RHContinuation.Network.recovered_lcm <;> assumption

#print axioms challenge_recovered_growth

end Lcm.v4
