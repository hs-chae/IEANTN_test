/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCertificateCode
import RamanujanPV.HighBudgetControlO.Gaps
import RamanujanPV.HighBudgetControlO.Data0000
import RamanujanPV.HighBudgetControlO.Data0001
namespace RamanujanPV.HighBudgetControlO
open QuotientDemandCheck QuotientPackedDemand
noncomputable def rawNodes : Lean.RArray Nat := (.branch 128 raw_0000 raw_0001)
noncomputable def nodes : Lean.RArray Entry := unpack rawNodes
def entryCount : Nat := 190
end RamanujanPV.HighBudgetControlO
