/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.DirectLambda
import IEANTNQRHBridge

namespace LambdaActual

theorem direct_lambda330
    (hCH2 : LambdaEvolutionA.DirectCH2Inputs)
    (hPrimary : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x : ℝ} (hx : Real.exp (330 : ℝ)≤x) :
    |CH2.v1.lambdaSum x-(Real.log x-Real.eulerMascheroniConstant)| ≤
      (1826923053/200000000000 : ℝ)*x^(-(1 : ℝ)/8) :=
  LambdaEvolutionA.direct_lambda330 hCH2 hPrimary hRH OpenAIQRH.v1.local_pinned_replay hx

end LambdaActual
#print axioms LambdaActual.direct_lambda330
