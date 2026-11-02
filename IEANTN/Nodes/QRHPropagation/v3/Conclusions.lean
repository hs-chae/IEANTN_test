/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
namespace QRHPropagation.v3
open Real IEANTN
/-- Same shape and threshold as the frozen FKS2 application, with the coefficient proved from QRH. -/
def psi_classical_bound : Prop :=
  HasClassicalBound Eψ 0.0000000001 (3/2) 2 5.5666305 (exp 300)
end QRHPropagation.v3
