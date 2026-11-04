/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import RamanujanGapV3.Consumer
import RamanujanBudget.Provider

/-!
# Replay: the consumer applied to the actual program provider

`RamanujanGap.v3.challenge_ramanujan` takes the π expansion and the budget as premises. Here the
budget premise is discharged by the generated `RamanujanNumerics.v3` provider itself (one native
certificate). The π expansion `DudekPlattNumerics.v5.pi_two_sided_qrh` stays a premise, exactly
as in the node graph; its own solution is not imported, because its closure compiles the CH2.v6
density certificates.
-/

theorem RamanujanGap.v3.ramanujan_from_pi (hp : DudekPlattNumerics.v5.pi_two_sided_qrh) :
    RamanujanGap.v3.ramanujan :=
  RamanujanGap.v3.challenge_ramanujan hp RamanujanNumerics.v3.Provider.epsilon_budget
