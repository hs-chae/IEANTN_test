/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import RamanujanBudget.Provider

/-!
# Solution: `RamanujanNumerics.v3`

The provider module `RamanujanBudget/Provider.lean` is generated from
`scripts/native_assisted/providers.json` by `scripts/native_assisted/pv_update.py`. It holds the
selected file, the literals and one certificate; the proof is the shared family theorem
`PVRamanujan.budget_of_check` in `Solutions/ProgramVerification`.
-/

theorem RamanujanNumerics.v3.challenge_epsilon_budget : RamanujanNumerics.v3.epsilon_budget :=
  RamanujanNumerics.v3.Provider.epsilon_budget
