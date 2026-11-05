/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.RefinedConsumer
import PVEvolutionA.SlopedRay300
import PVEvolutionA.SlopedRay330
import PVEvolutionA.SlopedRayMid
namespace PVEvolutionA
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def C300 : ℝ := (1+33/10000000000000000)*(9468285637/1000000000000)+1/10000000000000000000000000000+1/10000000000000
noncomputable def C330 : ℝ := (1+33/10000000000000000)*(9150520022/1000000000000)+1/10000000000000000000000000000+1/10000000000000
noncomputable def Cmid : ℝ := (1+33/10000000000000000)*(9145877463/1000000000000)+1/10000000000000000000000000000+1/10000000000000
theorem coefficient_values :
    C300=(47341428185500156226713011/5000000000000000000000000000:ℝ) ∧
    C330=(91505200221000301967160727/10000000000000000000000000000:ℝ) ∧
    Cmid=(2286469365775007545348907/250000000000000000000000000:ℝ) := by
  norm_num [C300,C330,Cmid]

noncomputable def scale (x:ℝ) : ℝ := x^(-(1:ℝ)/8)
noncomputable def bound (x:ℝ) : ℝ :=
  if exp (661/2:ℝ)≤x then Cmid*scale x
  else if exp (330:ℝ)≤x then C330*scale x else C300*scale x
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
  apply Refined.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤300)
  exact SlopedRay300.coefficient
/-- Actual Epi consequence of the newly accepted source-linked expression. -/
theorem pi330_exact : HasPowerLogBound Eπ C330 0 (7/8) (exp 330) := by
  unfold C330
  apply Refined.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤330)
  exact SlopedRay330.coefficient
/-- Actual Epi consequence of the newly accepted source-linked expression. -/
theorem pimid_exact : HasPowerLogBound Eπ Cmid 0 (7/8) (exp (661/2)) := by
  unfold Cmid
  apply Refined.pi_from_graded_coefficient hCHJ hrvm hsmall hlow h hRH hQRH
    (by decide : 0<(65536:ℕ)) (by norm_num : (300:ℝ)≤(661/2))
  exact SlopedRayMid.coefficient
/-- The public provider keeps every proved ray and selects the tighter applicable cap. -/
theorem pi_evolved {x:ℝ} (hx:exp (300:ℝ)≤x) : Eπ x≤bound x := by
  unfold bound
  split_ifs with hm hd
  · have hp:=pimid_exact hCHJ hrvm hsmall hlow h hRH hQRH x hm
    simpa only [scale,pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hp
  · have hp:=pi330_exact hCHJ hrvm hsmall hlow h hRH hQRH x hd
    simpa only [scale,pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hp
  · have hp:=pi300_exact hCHJ hrvm hsmall hlow h hRH hQRH x hx
    simpa only [scale,pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hp
end OriginalInputs
#print axioms pi300_exact
#print axioms pi330_exact
#print axioms pimid_exact
#print axioms pi_evolved
end PVEvolutionA
