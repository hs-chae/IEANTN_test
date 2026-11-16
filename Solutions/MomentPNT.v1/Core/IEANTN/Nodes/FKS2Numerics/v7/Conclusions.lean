/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
namespace FKS2Numerics.v7
open Real IEANTN
/-- Original QRH30-cell allowance, now consumed through the shared generic transport. -/
def qrh_pi : Prop := HasNumericalBound Eπ ((5:ℝ)/10^16) (exp 330)
end FKS2Numerics.v7
