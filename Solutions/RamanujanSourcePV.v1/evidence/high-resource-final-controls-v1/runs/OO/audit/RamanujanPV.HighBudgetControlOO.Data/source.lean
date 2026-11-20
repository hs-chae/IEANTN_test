/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCertificateCode
import RamanujanPV.HighBudgetControlOO.Gaps
import RamanujanPV.HighBudgetControlOO.Data0000
import RamanujanPV.HighBudgetControlOO.Data0001
namespace RamanujanPV.HighBudgetControlOO
open QuotientDemandCheck QuotientPackedDemand
noncomputable def rawNodes : Lean.RArray Nat := (.branch 128 raw_0000 raw_0001)
noncomputable def nodes : Lean.RArray Entry := unpack rawNodes
def entryCount : Nat := 190
end RamanujanPV.HighBudgetControlOO
