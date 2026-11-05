/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Consumer
import PVEvolutionA.Ray300
namespace PVEvolutionA.Fallback
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def C300 : ℝ := (1+1/1000000000)*(9468680078/1000000000000)+1/1000000000000+1/100000000
section OriginalInputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH
/-- Actual Epi consequence of the newly accepted source-linked expression. -/
theorem pi300_exact : HasPowerLogBound Eπ C300 0 (7/8) (exp 300) := by
  unfold C300
  apply PVEvolutionA.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤300)
  simpa only [show (300:ℝ)/3=100 by norm_num] using Ray300.coefficient
end OriginalInputs
#print axioms pi300_exact
end PVEvolutionA.Fallback
