/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LambdaEvolutionA.WithoutCotangent
import PVEvolutionA.Recovery.MixedProof
import IEANTNQRHBridge
namespace E1ActualTransport
open Real IEANTN WinnerDirectKernel
section Inputs
variable (hs:LambdaEvolutionA.DirectCH2Inputs12)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
include hs h hRH
 theorem psi330 {x:ℝ} (hx:exp (330:ℝ)≤x) :
  Eψ x≤(1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8) :=
  LambdaEvolutionA.psi_companion330_without_cotangent hs h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem lambda330 {x:ℝ} (hx:exp (330:ℝ)≤x) :
  |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)|≤
    (1826923053/200000000000:ℝ)*x^(-(1:ℝ)/8) :=
  LambdaEvolutionA.direct_lambda330_without_cotangent hs h hRH OpenAIQRH.v1.local_pinned_replay hx
 theorem pi330 (hCHJ:OriginalCHJSource) :
  HasPowerLogBound Eπ (9134616/1000000000) 0 (7/8) (exp 330) :=
  PVEvolutionA.Recovery.MixedProof.pi330_tight_friendly_of_checks
    hCHJ hs.hrvm hs.hsmall hs.hlow h hRH OpenAIQRH.v1.local_pinned_replay
    PVEvolutionA.Recovery.GaussianBasis.accepted
    PVEvolutionA.Recovery.Mixed.base_checked PVEvolutionA.Recovery.Mixed.checked_all
end Inputs
end E1ActualTransport
#print axioms E1ActualTransport.psi330
#print axioms E1ActualTransport.lambda330
#print axioms E1ActualTransport.pi330
