/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNW.v1.Tables

namespace BKLNW.v4
open Real IEANTN

noncomputable def tableCoefficient (b : ℕ) : ℝ :=
  if 1000 ≤ b then 0.01014 else if 512 ≤ b then 0.01117 else
  if 300 ≤ b then 0.01310 else if 256 ≤ b then 0.01411 else
  if 224 ≤ b then 0.01526 else 0.01713

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def table8_phase2 : Prop :=
  ∀ p ∈ BKLNW.v1.table8, 200 ≤ p.1 →
    HasNumericalBound Eψ (tableCoefficient p.1 * exp (-(p.1 : ℝ) / 8)) (exp p.1) ∧
    tableCoefficient p.1 * exp (-(p.1 : ℝ) / 8) < p.2

end BKLNW.v4
