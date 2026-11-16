/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNW.v1.Tables

/-! One general improvement of the existing table interface; the stored data is unchanged. -/
namespace BKLNW.v3
open Real IEANTN

/-- Every registered row at b>=200 has a smaller QRH allowance, valid on an unbounded ray. -/
def table8_qrh_replay : Prop :=
  ∀ p ∈ BKLNW.v1.table8, 200 ≤ p.1 →
    HasNumericalBound Eψ (0.01713 * exp (-(p.1 : ℝ) / 8)) (exp p.1) ∧
      0.01713 * exp (-(p.1 : ℝ) / 8) < p.2

end BKLNW.v3
