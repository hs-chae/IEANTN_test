/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms

namespace FKS2Numerics.v6
open Real IEANTN
/-- Reconstructed old30-cell C allowance on the full ray, conditional on the declared Table3 inputs and independent anchor. -/
def old_pi : Prop := HasNumericalBound Eπ 1.69e-12 (exp 330)
end FKS2Numerics.v6
