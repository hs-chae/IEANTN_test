/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.SlopedSpectral
import PVEvolutionA.TightTransfer
import WinnerDensityA.DirectRHResult
namespace PVEvolutionA.PointwiseConsumer
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
/-- The numerical premise is discharged by a new executed provider in Result.
It is not an additional external mathematical assumption in the final theorem. -/
theorem pi_from_graded_coefficient
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {n : ℕ} (hn : 0<n) {L0 C : ℝ} (h0 : 300≤L0)
    (hc : Sloped.coefficient n L0 (L0/3)≤C) :
    HasPowerLogBound Eπ ((1+33/10000000000000000)*C+1/10000000000000000000000000000+1/10000000000000)
      0 (7/8) (exp L0) := by
  apply Tight.rh_pi_ray_of_budgets hCHJ hQRH hlow h0
  · intro L hL
    exact (Sloped.graded_spectral_ray hrvm hsmall hlow h hRH hQRH hn h0 hL).trans hc
  · intro L hL
    exact Tight.low_kernel hQRH hRH hrvm hsmall hlow (h0.trans hL)
#print axioms pi_from_graded_coefficient
end PVEvolutionA.PointwiseConsumer
