/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujanUpdate.Provider
import ForwardRamanujanUpdate.Consumer
import ForwardRamanujan.Baseline

/-- Both real programs and both real mathematical consumers are supplied, with only the mathematical update left conditional. -/
theorem ForwardRamanujan.forward (hpsi : QRHCH2.v5.psi_refined_bound) :
    RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement :=
  ⟨RamanujanGap.v2.challenge_paired (ForwardRamanujan.Update.supplied_pi hpsi)
    RamanujanNumerics.v1.challenge_epsilon_budget RamanujanNumerics.v2.challenge_epsilon_budget,
   RamanujanGap.v2.challenge_strict_allowance_improvement⟩
