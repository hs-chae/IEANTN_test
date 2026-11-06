/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Comparison.Cumulative
namespace E1Comparison
open Real IEANTN WinnerDirectKernel

def toTwelve (hs:E1FrozenN.DirectCH2Inputs):LambdaEvolutionA.DirectCH2Inputs12:=
  ⟨hs.hfe,hs.hdig,hs.h24u,hs.h24l,hs.hk,hs.hneg,hs.h2v,hs.hv,
    hs.hrvm,hs.hsmall,hs.hlow,hs.hH⟩

theorem matched_pair (hs:E1FrozenN.DirectCH2Inputs)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    (Eψ x ≤ E1NPlus.finalPairBound x ∧ Eψ x ≤ pairBound x) ∧
    (|CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ E1NPlus.finalPairBound x ∧
      |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ pairBound x) ∧
    pairBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.finalPairBound x := by
  have hx300:exp (300:ℝ) ≤ x:=(exp_le_exp.mpr (by norm_num : (300:ℝ) ≤ 330)).trans hx.1
  have hn:=E1NPlus.final_pair hs h hRH hQRH hx300
  have he:=pair_full (toTwelve hs) h hRH hQRH hx300
  exact ⟨⟨hn.1,he.1⟩,⟨hn.2,he.2⟩,pair_strict_full hx⟩

theorem matched_pi (hs:E1FrozenN.DirectCH2Inputs) (hCHJ:OriginalCHJSource)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    Eπ x ≤ E1NPlus.piBound x ∧ Eπ x ≤ piBound x ∧
    piBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.piBound x := by
  have hx300:exp (300:ℝ) ≤ x:=(exp_le_exp.mpr (by norm_num : (300:ℝ) ≤ 330)).trans hx.1
  exact ⟨E1NPlus.pi_full hCHJ hs.hrvm hs.hsmall hs.hlow h hRH hQRH hx300,
    pi_full (toTwelve hs) h hRH hQRH hCHJ hx300,pi_strict_full hx⟩
#print axioms matched_pair
#print axioms matched_pi
end E1Comparison
