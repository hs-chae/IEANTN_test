/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Reuse of the actual existing IEANTN source proof; no new source predicate. -/
import ZetaReal01
namespace RHContinuation.MobiusRealZeros
 theorem at_half : riemannZeta ((1/2:ℝ):ℂ)≠0 :=
  CH2ZetaReal.riemannZeta_ne_zero_Ico (by norm_num) (by norm_num)
#print axioms at_half
end RHContinuation.MobiusRealZeros
