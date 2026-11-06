/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Conditional prime-counting provider consuming actual source-linked finite runs. -/
import PVEvolutionA.Recovery.ResultProof
import PVEvolutionA.Recovery.GaussianBasisRun
import PVEvolutionA.Recovery.RayRun
import PVEvolutionA.Recovery.PVFloorResult
namespace PVEvolutionA.Recovery
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0

/-- Keep the complete old function and add the new ray where applicable. -/
noncomputable def recoveredBound (x : ℝ) : ℝ :=
  if exp (330:ℝ)≤x then min (PVEvolutionA.bestBound x) (friendlyC*PVEvolutionA.scale x)
  else PVEvolutionA.bestBound x

section Inputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH

theorem pi330_exact : HasPowerLogBound Eπ certifiedC 0 (7/8) (exp 330) :=
  pi330_of_checks hCHJ hrvm hsmall hlow h hRH hQRH GaussianBasis.accepted Ray.checked

theorem pi330_friendly : HasPowerLogBound Eπ friendlyC 0 (7/8) (exp 330) :=
  pi330_friendly_of_checks hCHJ hrvm hsmall hlow h hRH hQRH GaussianBasis.accepted Ray.checked

theorem pi330_explicit {x : ℝ} (hx : exp (330:ℝ)≤x) :
    Eπ x≤(91347/10000000:ℝ)*x^(-(1:ℝ)/8) := by
  have hp:=pi330_friendly hCHJ hrvm hsmall hlow h hRH hQRH x hx
  simpa only [friendlyC,pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hp

theorem pi_recovered {x : ℝ} (hx : exp (300:ℝ)≤x) : Eπ x≤recoveredBound x := by
  have ho:=PVEvolutionA.pi_best hCHJ hrvm hsmall hlow h hRH hQRH hx
  unfold recoveredBound
  split_ifs with h330
  · apply le_min ho
    simpa only [friendlyC,PVEvolutionA.scale] using
      pi330_explicit hCHJ hrvm hsmall hlow h hRH hQRH h330
  · exact ho

theorem full_D_result {x : ℝ} (hx : ScopedWinnerA.Comparison.domain x) :
    Eπ x≤friendlyC*PVEvolutionA.scale x ∧
    friendlyC*PVEvolutionA.scale x+(2/1000000:ℝ)*PVEvolutionA.scale x<
      PVEvolutionA.bestBound x ∧
    ∀i:Fin 39, friendlyC*PVEvolutionA.scale x<ScopedWinnerA.Coverage.allowance x i := by
  refine ⟨?_,?_,?_⟩
  · simpa only [friendlyC,PVEvolutionA.scale] using
      pi330_explicit hCHJ hrvm hsmall hlow h hRH hQRH hx.1
  · simpa only [friendlyC] using PVFloor.strict_full_comparison_checked hx
  · intro i
    simpa only [friendlyC] using PVFloor.strict_all39_checked hx i
end Inputs
#print axioms pi330_exact
#print axioms pi330_friendly
#print axioms pi330_explicit
#print axioms pi_recovered
#print axioms full_D_result
end PVEvolutionA.Recovery
