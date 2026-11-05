/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import RamanujanBudget.Provider

/-!
# Challenge theorem of `RamanujanNumerics.v3`

In its own module, with a name no other solution uses: Lake puts this package last on the module
search path, so `import Solution` from here would load another solution's `Solution` module first.
`comparator.json` names this module as `solution_module`.
-/

theorem RamanujanNumerics.v3.challenge_epsilon_budget : RamanujanNumerics.v3.epsilon_budget :=
  RamanujanNumerics.v3.Provider.epsilon_budget
