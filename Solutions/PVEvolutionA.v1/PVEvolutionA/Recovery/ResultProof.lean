/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.Consumer
import PVEvolutionA.Recovery.RayProgram
namespace PVEvolutionA.Recovery
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def certifiedC : ℝ :=
  (1+33/10000000000000000)*(9134699/1000000000)+
    1/10000000000000000000000000000+1/10000000000000
noncomputable def friendlyC : ℝ := 91347/10000000

theorem coefficient_rounding : certifiedC≤friendlyC := by norm_num [certifiedC,friendlyC]

section Inputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH

theorem pi330_of_checks
    (hGaussian : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (hRay : WinnerProgramA.acceptUpper Ray.output Ray.bounds=true) :
    HasPowerLogBound Eπ certifiedC 0 (7/8) (exp 330) := by
  unfold certifiedC
  apply Consumer.pi_from_graded_coefficient hGaussian hCHJ hrvm hsmall hlow h hRH hQRH
    (by norm_num [Ray.sigmaCells] : 0<Ray.sigmaCells) (by norm_num : (300:ℝ)≤330)
  exact Ray.coefficient_of_execution Ray.output Ray.execution hRay

theorem pi330_friendly_of_checks
    (hGaussian : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (hRay : WinnerProgramA.acceptUpper Ray.output Ray.bounds=true) :
    HasPowerLogBound Eπ friendlyC 0 (7/8) (exp 330) := by
  intro x hx
  have hp:=pi330_of_checks hCHJ hrvm hsmall hlow h hRH hQRH hGaussian hRay x hx
  have hxpos : 0<x := (exp_pos _).trans_le hx
  simp only [pow_zero,mul_one] at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right coefficient_rounding
    (rpow_nonneg hxpos.le _))
end Inputs
#print axioms pi330_of_checks
#print axioms pi330_friendly_of_checks
end PVEvolutionA.Recovery
