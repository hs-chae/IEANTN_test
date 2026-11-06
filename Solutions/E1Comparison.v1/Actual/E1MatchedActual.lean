/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Comparison.Matched
import IEANTNQRHBridge
namespace E1MatchedActual
open Real IEANTN WinnerDirectKernel
 theorem pair (hs:E1FrozenN.DirectCH2Inputs)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    (Eψ x ≤ E1NPlus.finalPairBound x ∧ Eψ x ≤ E1Comparison.pairBound x) ∧
    (|CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ E1NPlus.finalPairBound x ∧
      |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ E1Comparison.pairBound x) ∧
    E1Comparison.pairBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.finalPairBound x:=
  E1Comparison.matched_pair hs h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem pi (hs:E1FrozenN.DirectCH2Inputs) (hCHJ:OriginalCHJSource)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    Eπ x ≤ E1NPlus.piBound x ∧ Eπ x ≤ E1Comparison.piBound x ∧
    E1Comparison.piBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.piBound x:=
  E1Comparison.matched_pi hs hCHJ h hRH OpenAIQRH.v1.local_pinned_replay hx
#print axioms pair
#print axioms pi
end E1MatchedActual
