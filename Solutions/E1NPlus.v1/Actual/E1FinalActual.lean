/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Downstream
import E1Comparison.Cumulative
import E1NPlusActual
namespace E1FinalActual
open Real IEANTN WinnerDirectKernel
section
variable (hs:E1FrozenN.DirectCH2Inputs)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
include hs h hRH
 theorem nplus_pair {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    Eψ x ≤ E1NPlus.finalPairBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ E1NPlus.finalPairBound x:=
  E1NPlus.final_pair hs h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem nplus_pi (hCHJ:OriginalCHJSource) {x:ℝ} (hx:exp (300:ℝ) ≤ x):Eπ x ≤ E1NPlus.piBound x:=
  E1NPlus.pi_full hCHJ hs.hrvm hs.hsmall hs.hlow h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem ramanujan:RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement:=
  E1NPlus.ramanujan hs h hRH OpenAIQRH.v1.local_pinned_replay
end
section
variable (hs:LambdaEvolutionA.DirectCH2Inputs12)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
include hs h hRH
 theorem treatment_pair {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    Eψ x ≤ E1Comparison.pairBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ E1Comparison.pairBound x:=
  E1Comparison.pair_full hs h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem treatment_pi (hCHJ:OriginalCHJSource) {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    Eπ x ≤ E1Comparison.piBound x:=
  E1Comparison.pi_full hs h hRH OpenAIQRH.v1.local_pinned_replay hCHJ hx
end
#print axioms nplus_pair
#print axioms nplus_pi
#print axioms ramanujan
#print axioms treatment_pair
#print axioms treatment_pi
end E1FinalActual
