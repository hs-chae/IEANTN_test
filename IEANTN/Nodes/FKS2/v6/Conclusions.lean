/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
/-! Historical FKS2 Table4 allowances. Literature inputs, not verified C outputs. -/
namespace FKS2.v6
open Real IEANTN
def table4_anchor_300 : Prop := Eπ (exp 300) ≤ 1.6997e-12
def table4_330 : Prop := HasNumericalBound Eπ 1.6855e-12 (exp 330)
end FKS2.v6
