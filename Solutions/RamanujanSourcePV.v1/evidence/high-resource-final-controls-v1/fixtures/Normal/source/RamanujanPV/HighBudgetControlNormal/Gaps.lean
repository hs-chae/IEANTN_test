/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCertificateCode
namespace RamanujanPV.HighBudgetControlNormal
open QuotientDemandCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable def gaps : Lean.RArray Gap := (.branch 6 (.branch 3 (.branch 1 (.leaf ⟨2,2,[]⟩) (.branch 2 (.leaf ⟨3,3,[]⟩) (.leaf ⟨4,5,[2]⟩))) (.branch 4 (.leaf ⟨6,7,[2]⟩) (.branch 5 (.leaf ⟨8,11,[2,3,2]⟩) (.leaf ⟨12,13,[2]⟩)))) (.branch 9 (.branch 7 (.leaf ⟨14,17,[2,3,2]⟩) (.branch 8 (.leaf ⟨18,19,[2]⟩) (.leaf ⟨20,23,[2,3,2]⟩))) (.branch 10 (.leaf ⟨24,29,[2,5,2,3,2]⟩) (.branch 11 (.leaf ⟨30,31,[2]⟩) (.leaf ⟨32,32,[]⟩)))))
def gapCount : Nat := 12
end RamanujanPV.HighBudgetControlNormal
