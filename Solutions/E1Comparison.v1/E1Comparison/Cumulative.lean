/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1Comparison.Strict
namespace E1Comparison
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def pairBound (x:ℝ):ℝ:=if exp (330:ℝ) ≤ x then
  min (E1NPlus.finalPairBound x) (E1Evolved.kappa*x^(-(1:ℝ)/8)) else E1NPlus.finalPairBound x
noncomputable def piBound (x:ℝ):ℝ:=if exp (330:ℝ) ≤ x then
  min (E1NPlus.piBound x) ((9134616/1000000000:ℝ)*PVEvolutionA.scale x) else E1NPlus.piBound x
section
variable (hs:LambdaEvolutionA.DirectCH2Inputs12)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
  (hQRH:ZetaZeroFreeHalfPlane (7/8))
include hs h hRH hQRH
theorem pair_full {x:ℝ} (hx:exp (300:ℝ) ≤ x):
    Eψ x ≤ pairBound x ∧ |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)| ≤ pairBound x := by
  have hn:=E1NPlus.final_pair (E1Evolved.frozenInputs hs) h hRH hQRH hx
  unfold pairBound
  split_ifs with h330
  · have he:=E1Evolved.evolved_pair hs h hRH hQRH h330
    have hp:=he.1.trans (min_le_right _ _)
    have hw:=he.2.trans (min_le_right _ _)
    exact ⟨le_min hn.1 hp,le_min hn.2 hw⟩
  · exact hn

theorem pi_full (hCHJ:OriginalCHJSource) {x:ℝ} (hx:exp (300:ℝ) ≤ x):Eπ x ≤ piBound x := by
  have hn:=E1NPlus.pi_full hCHJ hs.hrvm hs.hsmall hs.hlow h hRH hQRH hx
  unfold piBound
  split_ifs with h330
  · have he:=E1Evolved.evolved_pi hs h hRH hQRH hCHJ hx
    rw [E1Evolved.piBound,if_pos h330] at he
    exact le_min hn (he.trans (min_le_right _ _))
  · exact hn
end

theorem pair_strict_full {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    pairBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.finalPairBound x := by
  unfold pairBound
  rw [if_pos hx.1]
  have hm:min (E1NPlus.finalPairBound x) (E1Evolved.kappa*x^(-(1:ℝ)/8)) ≤ E1Evolved.kappa*PVEvolutionA.scale x:=min_le_right _ _
  linarith [pair_strict hx]

theorem pi_strict_full {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x):
    piBound x+(2/1000000:ℝ)*PVEvolutionA.scale x<E1NPlus.piBound x := by
  unfold piBound
  rw [if_pos hx.1]
  have hm:min (E1NPlus.piBound x) ((9134616/1000000000:ℝ)*PVEvolutionA.scale x) ≤ (9134616/1000000000:ℝ)*PVEvolutionA.scale x:=min_le_right _ _
  linarith [pi_strict hx]
#print axioms pair_full
#print axioms pi_full
#print axioms pair_strict_full
#print axioms pi_strict_full
end E1Comparison
