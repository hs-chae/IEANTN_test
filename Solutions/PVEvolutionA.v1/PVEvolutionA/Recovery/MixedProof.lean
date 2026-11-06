/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.MixedProgram
import PVEvolutionA.Recovery.ResultProof
namespace PVEvolutionA.Recovery.MixedProof
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def tightC : ℝ :=
  (1+33/10000000000000000)*(1826923053/200000000000)+
    1/10000000000000000000000000000+1/10000000000000
noncomputable def tightFriendly : ℝ := 9134616/1000000000
 theorem tight_rounding : tightC≤tightFriendly := by norm_num [tightC,tightFriendly]
section Inputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH
 theorem pi330_tight_of_checks
    (hGaussian : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (hbase : Chunks.baseAccepted=true)
    (hc : ∀i:Fin Chunks.count,Mixed.accepted i.val=true) :
    HasPowerLogBound Eπ tightC 0 (7/8) (exp 330) := by
  unfold tightC
  apply Consumer.pi_from_graded_coefficient hGaussian hCHJ hrvm hsmall hlow h hRH hQRH
    (by norm_num [Ray.sigmaCells] : 0<Ray.sigmaCells) (by norm_num : (300:ℝ)≤330)
  exact Mixed.coefficient_of_checks hbase hc
 theorem pi330_tight_friendly_of_checks
    (hGaussian : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (hbase : Chunks.baseAccepted=true)
    (hc : ∀i:Fin Chunks.count,Mixed.accepted i.val=true) :
    HasPowerLogBound Eπ tightFriendly 0 (7/8) (exp 330) := by
  intro x hx
  have hp:=pi330_tight_of_checks hCHJ hrvm hsmall hlow h hRH hQRH hGaussian hbase hc x hx
  have hxpos : 0<x := (exp_pos _).trans_le hx
  simp only [pow_zero,mul_one] at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right tight_rounding (rpow_nonneg hxpos.le _))
end Inputs
#print axioms pi330_tight_of_checks
end PVEvolutionA.Recovery.MixedProof
