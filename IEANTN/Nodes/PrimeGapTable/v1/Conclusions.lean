/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOnePrimeEvolution

namespace PrimeGapTable.v1
/-- Reported consecutive-prime gaps below 2^64, maximal1550, from Nicely2019. A historical computation premise; its completeness/practical-verification qualifications remain external. -/
def gaps : Prop := IEANTN.RHOnePrimeEvolution.finiteGapTable
end PrimeGapTable.v1
