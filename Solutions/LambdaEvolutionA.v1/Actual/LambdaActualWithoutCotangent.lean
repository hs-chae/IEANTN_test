/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.WithoutCotangent
import IEANTNQRHBridge

namespace LambdaActualWithoutCotangent

theorem direct_lambda330
    (hs : LambdaEvolutionA.DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) :=
  LambdaEvolutionA.direct_lambda330_without_cotangent hs h hRH
    OpenAIQRH.v1.local_pinned_replay hx

theorem psi_companion330
    (hs : LambdaEvolutionA.DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    IEANTN.Eψ x ≤ (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) :=
  LambdaEvolutionA.psi_companion330_without_cotangent hs h hRH
    OpenAIQRH.v1.local_pinned_replay hx

theorem matched_flat_lambda330
    (hs : LambdaEvolutionA.DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8) :=
  LambdaEvolutionA.matched_flat_lambda330_without_cotangent hs h hRH
    OpenAIQRH.v1.local_pinned_replay hx

theorem matched_direct_and_flat330
    (hs : LambdaEvolutionA.DirectCH2Inputs12)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {x : ℝ} (hx : Real.exp (330 : ℝ) ≤ x) :
    (|CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8)) ∧
    (|CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8)) ∧
    ((1826923053/200000000000 : ℝ) * x ^ (-(1 : ℝ)/8) <
      (9 * (1826923053/200000000000 : ℝ)) * x ^ (-(1 : ℝ)/8)) :=
  LambdaEvolutionA.matched_direct_and_flat330_without_cotangent hs h hRH
    OpenAIQRH.v1.local_pinned_replay hx

end LambdaActualWithoutCotangent

#print axioms LambdaActualWithoutCotangent.direct_lambda330
#print axioms LambdaActualWithoutCotangent.psi_companion330
#print axioms LambdaActualWithoutCotangent.matched_flat_lambda330
#print axioms LambdaActualWithoutCotangent.matched_direct_and_flat330
