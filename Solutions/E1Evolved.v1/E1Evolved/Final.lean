/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Final
import LambdaEvolutionA.WithoutCotangent
import HighAnchorIntervalB.Result
import PVEvolutionA.Recovery.MixedProof
import PVEvolutionA.Recovery.PVFloorResult
namespace E1Evolved
open Real IEANTN WinnerDirectKernel
noncomputable def kappa : ℝ := 1826923053/200000000000
noncomputable def pairBound (x:ℝ) : ℝ :=
  min (E1FrozenN.finalErrorBound x) (kappa*x^(-(1:ℝ)/8))
noncomputable def piBound (x:ℝ) : ℝ :=
  if exp (330:ℝ)≤x then
    min (PVEvolutionA.bestBound x) ((9134616/1000000000:ℝ)*PVEvolutionA.scale x)
  else PVEvolutionA.bestBound x

theorem frozenInputs (h:LambdaEvolutionA.DirectCH2Inputs12) : E1FrozenN.DirectCH2Inputs :=
  let q:=h.toDirect
  ⟨q.hfe,q.hdig,q.h24u,q.h24l,q.hk,q.hneg,q.h2v,q.hv,q.hcs,q.hrvm,q.hsmall,q.hlow,q.hH⟩
section Inputs
variable
  (hs:LambdaEvolutionA.DirectCH2Inputs12)
  (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
  (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
  (hQRH:ZetaZeroFreeHalfPlane (7/8))
include hs h hRH hQRH

theorem evolved_pair {x:ℝ} (hx:exp (330:ℝ)≤x) :
    Eψ x≤pairBound x ∧
    |CH2.v1.lambdaSum x-(log x-eulerMascheroniConstant)|≤pairBound x := by
  have hn:=E1FrozenN.final_pair (frozenInputs hs) h hRH hQRH hx
  exact ⟨le_min hn.1 (LambdaEvolutionA.psi_companion330_without_cotangent hs h hRH hQRH hx),
    le_min hn.2 (LambdaEvolutionA.direct_lambda330_without_cotangent hs h hRH hQRH hx)⟩

theorem evolved_pi (hCHJ:OriginalCHJSource) {x:ℝ} (hx:exp (300:ℝ)≤x) :
    Eπ x≤piBound x := by
  have ho:=PVEvolutionA.pi_best hCHJ hs.hrvm hs.hsmall hs.hlow h hRH hQRH hx
  unfold piBound
  split_ifs with h330
  · apply le_min ho
    have hp:=PVEvolutionA.Recovery.MixedProof.pi330_tight_friendly_of_checks
      hCHJ hs.hrvm hs.hsmall hs.hlow h hRH hQRH
      PVEvolutionA.Recovery.GaussianBasis.accepted
      PVEvolutionA.Recovery.Mixed.base_checked PVEvolutionA.Recovery.Mixed.checked_all x h330
    simpa only [PVEvolutionA.Recovery.MixedProof.tightFriendly,HasPowerLogBound,
      pow_zero,mul_one,PVEvolutionA.scale,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hp
  · exact ho
end Inputs

theorem coefficient_strict {x:ℝ} (hx:0<x) :
    kappa*x^(-(1:ℝ)/8)<
    (9150520021/1000000000000+1/10^28:ℝ)*x^(-(1:ℝ)/8) := by
  exact mul_lt_mul_of_pos_right (by norm_num [kappa]) (rpow_pos_of_pos hx _)

theorem pi_full_closed_domain_strict {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    (9134616/1000000000:ℝ)*PVEvolutionA.scale x+
      (2/1000000:ℝ)*PVEvolutionA.scale x<PVEvolutionA.bestBound x := by
  have hs:0≤PVEvolutionA.scale x:=rpow_nonneg ((exp_pos _).trans_le hx.1).le _
  have hm:=mul_le_mul_of_nonneg_right
    (by norm_num : (9134616/1000000000:ℝ)≤91347/10000000) hs
  linarith [PVEvolutionA.Recovery.PVFloor.strict_full_comparison_checked hx]

#print axioms evolved_pair
#print axioms evolved_pi
#print axioms pi_full_closed_domain_strict
end E1Evolved
