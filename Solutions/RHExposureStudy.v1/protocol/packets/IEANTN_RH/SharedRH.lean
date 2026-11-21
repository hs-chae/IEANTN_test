/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! The exact shared hypothesis for both arms. No project-specific interface or theorem. -/
namespace SharedRH

/-- Exactly the pinned Mathlib assertion, retained as an explicit downstream parameter. -/
def hypothesis : Prop := RiemannHypothesis

end SharedRH
