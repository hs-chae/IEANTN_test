/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectRHResult
namespace PVEvolutionA.Tight
open Real Set MeasureTheory IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
 theorem remainders {L : ℝ} (hL : 300≤L) :
    ((13/2:ℝ)*L/exp (L/3)*(1+1/((3/4)*L))+4*L*exp (-(L/4))+
      (L^2+2*L)*exp (-L/2))*exp (L/8)≤1/10000000000000 := by
  have hLp : 0<L := by linarith
  have hv : 1≤(3/4:ℝ)*L := by linarith
  have hi : 1/((3/4:ℝ)*L)≤1 := (div_le_one (by positivity)).mpr hv
  have hlin := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0:=(300:ℝ)) (c:=1/8) (by norm_num) (by norm_num) hL
  have hlin2 := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 1
    (L0:=(300:ℝ)) (c:=1/5) (by norm_num) (by norm_num) hL
  have hquad := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 2
    (L0:=(300:ℝ)) (c:=1/4) (by norm_num) (by norm_num) hL
  have he37 : exp (-(300:ℝ)/8)≤1/(2:ℝ)^54 := by
    have h75 : (2:ℝ)^108≤exp (75:ℝ) := by
      have hh:=(CH2Section7A.exp_nat_bounds 75).1
      norm_num at hh ⊢
      linarith
    have heq : exp ((300:ℝ)/8)^2=exp (75:ℝ) := by
      rw [pow_two,←exp_add]
      norm_num
    have hs : ((2:ℝ)^54)^2≤exp ((300:ℝ)/8)^2 := by
      rw [heq]
      convert h75 using 1 <;> norm_num
    have hh : (2:ℝ)^54≤exp ((300:ℝ)/8) :=
      (sq_le_sq₀ (by positivity) (exp_pos _).le).mp hs
    rw [show -(300:ℝ)/8= -((300:ℝ)/8) by ring,exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ)<(2:ℝ)^54) hh
  have he60:=DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 60
  have he75:=DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 75
  have hA : 4*L*exp (-(L/8))≤1200/(2:ℝ)^54 := by
    norm_num only [pow_one] at hlin
    have hExpL : -(L/8)=-(1/8:ℝ)*L := by ring
    have hlin' : L*exp (-(1/8:ℝ)*L)≤300*exp (-(300:ℝ)/8) := by
      convert! hlin using 1 <;> norm_num
    calc _ = 4*(L*exp (-(1/8:ℝ)*L)) := by rw [hExpL];ring
         _ ≤ 4*(300*exp (-(300:ℝ)/8)) := mul_le_mul_of_nonneg_left hlin' (by norm_num)
         _ ≤ 4*(300*(1/(2:ℝ)^54)) := by gcongr
         _ = _ := by ring
  have hT : (13/2:ℝ)*L*exp (-(5/24)*L)*(1+1/((3/4)*L))≤3900/(2:ℝ)^60 := by
    have hexp : exp (-(5/24)*L)≤exp (-(1/5)*L) := exp_le_exp.mpr (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hexp hLp.le
    norm_num only [pow_one] at hlin2
    have he60' : exp (-(1/5:ℝ)*300)≤1/(2:ℝ)^60 := by convert he60 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he60' (by norm_num : (0:ℝ)≤300)
    have hbound : L*exp (-(5/24)*L)≤300/(2:ℝ)^60 := by linarith
    have hh2:=mul_le_mul hbound (by linarith : 1+1/((3/4:ℝ)*L)≤2)
      (by positivity) (by positivity : 0≤300/(2:ℝ)^60)
    nlinarith
  have hP : (L^2+2*L)*exp (-(3/8)*L)≤181200/(2:ℝ)^75 := by
    have hx : L^2+2*L≤2*L^2 := by nlinarith
    have he : exp (-(3/8)*L)≤exp (-(1/4)*L) := exp_le_exp.mpr (by linarith)
    have hp:=mul_le_mul hx he (exp_pos _).le (by positivity : 0≤2*L^2)
    have he75' : exp (-(1/4:ℝ)*300)≤1/(2:ℝ)^75 := by convert he75 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he75' (by norm_num : (0:ℝ)≤(300:ℝ)^2)
    nlinarith
  have heq :
      ((13/2:ℝ)*L/exp (L/3)*(1+1/((3/4)*L))+4*L*exp (-(L/4))+
        (L^2+2*L)*exp (-L/2))*exp (L/8)=
      (13/2)*L*exp (-(5/24)*L)*(1+1/((3/4)*L))+4*L*exp (-(L/8))+
        (L^2+2*L)*exp (-(3/8)*L) := by
    rw [div_eq_mul_inv,←exp_neg]
    simp only [add_mul]
    have h1 : exp (-(L/3))*exp (L/8)=exp (-(5/24)*L) := by rw [←exp_add];congr 1;ring
    have h2 : exp (-(L/4))*exp (L/8)=exp (-(L/8)) := by rw [←exp_add];congr 1;ring
    have h3 : exp (-L/2)*exp (L/8)=exp (-(3/8)*L) := by rw [←exp_add];congr 1;ring
    calc
      _ = (13/2:ℝ)*L*(exp (-(L/3))*exp (L/8))*(1+1/((3/4)*L))+
        4*L*(exp (-(L/4))*exp (L/8))+(L^2+2*L)*(exp (-L/2)*exp (L/8)) := by ring
      _ = _ := by rw [h1,h2,h3];ring
  rw [heq]
  norm_num at hA hT hP ⊢
  linarith


theorem rh_high_factor {L : ℝ} (hL : 300 ≤ L) :
    highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L ≤
      1+33/10000000000000000 := by
  have hLp : 0 < L := by linarith
  have hvp : 0 < (3/4:ℝ)*L := by positivity
  have hH : 0 < WinnerOriginalScalars.height := by norm_num [WinnerOriginalScalars.height]
  have he : exp (-(1/8:ℝ)*(L-(3/4)*L)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have h1 : 1/(WinnerOriginalScalars.height*L) ≤ 1/(WinnerOriginalScalars.height*300) := by gcongr
  have hfrac2 : L/(WinnerOriginalScalars.height*((3/4)*L)^2)=
      16/(9*WinnerOriginalScalars.height*L) := by field_simp;ring
  have hfrac3 : 2*L/(WinnerOriginalScalars.height*(1/8)*((3/4)*L)^3)=
      1024/(27*WinnerOriginalScalars.height*L^2) := by field_simp;ring
  have h2 : exp (-(1/8:ℝ)*(L-(3/4)*L))*L/(WinnerOriginalScalars.height*((3/4)*L)^2) ≤
      16/(9*WinnerOriginalScalars.height*300) := by
    calc _ ≤ L/(WinnerOriginalScalars.height*((3/4)*L)^2) := by
           apply div_le_div_of_nonneg_right _ (by positivity)
           simpa using mul_le_mul_of_nonneg_right he hLp.le
         _ = _ := hfrac2
         _ ≤ _ := by gcongr
  have h3 : 2*L/(WinnerOriginalScalars.height*(1/8)*((3/4)*L)^3) ≤
      1024/(27*WinnerOriginalScalars.height*(300:ℝ)^2) := by
    rw [hfrac3]
    gcongr
  unfold highFactor
  norm_num [WinnerOriginalScalars.height] at h1 h2 h3 ⊢
  linarith


theorem high_kernel_normalized (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C : ℝ} (hL : 300 ≤ L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C) :
    ‖∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
        (1+33/10000000000000000)*C := by
  have hLp : 0 < L := by linarith
  have hv : 0 < (3/4:ℝ)*L := by positivity
  have hvL : (3/4:ℝ)*L ≤ L := by linarith
  have hT : 0 < exp (L/3) := exp_pos _
  have hBound:=high_paired_kernel_bound hqrh hlow hT hv hvL
  have hm:=mul_le_mul_of_nonneg_right hBound (by positivity : 0 ≤ (L/exp L)*exp (L/8))
  have heq : (highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
      (exp L*WinnerDensityA.rawSpectral (exp (L/3)) (exp L))/L)*
        ((L/exp L)*exp (L/8))=
      highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
        (WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)) := by
    field_simp [hLp.ne',exp_ne_zero]
  rw [heq] at hm
  have hPaired : 0 ≤ pairedPsiBudget (exp (L/3)) L := by
    unfold pairedPsiBudget
    apply Finset.sum_nonneg
    intro q hq
    have hw:=(pair_properties hqrh hlow hq).1
    positivity
  have hRaw : 0 ≤ WinnerDensityA.rawSpectral (exp (L/3)) (exp L) :=
    nonneg_of_mul_nonneg_right (hPaired.trans (paired_budget_le_raw hT)) (exp_pos L)
  have hFactor:=mul_le_mul_of_nonneg_right (rh_high_factor hL)
    (mul_nonneg hRaw (exp_pos (L/8)).le)
  have hCap:=mul_le_mul_of_nonneg_left hSpectral
    (by norm_num : (0:ℝ) ≤ 1+33/10000000000000000)
  have hml : ‖∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
      highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
        (WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)) := by
    convert! hm using 1 <;> ring
  exact hml.trans (hFactor.trans hCap)


theorem low_kernel
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L : ℝ} (hL : 300≤L) :
    ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖*
      (L/exp L)*exp (L/8) ≤ 1/10000000000000000000000000000 := by
  have hLp : 0<L := by linarith
  have hT : 14≤exp (L/3) := by linarith [add_one_le_exp (L/3)]
  have hB:=low_paired_budget_bound hqrh hRH hrvm hsmall hlow (L:=L) hT
  rw [log_exp] at hB
  have hpol : (L/3)^2/(4*Real.pi)+(L/3)/(2*Real.pi)≤L^2+L := by
    have h1 : (L/3)^2/(4*Real.pi)≤(L/3)^2 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    have h2 : (L/3)/(2*Real.pi)≤L/3 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    nlinarith
  have hB' := hB.trans (mul_le_mul_of_nonneg_left hpol (by positivity : 0≤2*exp (L/2)))
  have hk:=high_sum_bound (lowPairedZeros (exp (L/3))) pairZ pairW
    (by norm_num : (0:ℝ)<1/8) (by norm_num : (0:ℝ)<14)
    (by positivity : 0<(3/4:ℝ)*L) (by linarith : (3/4:ℝ)*L≤L)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).1)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).2.1)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).2.2)
  have hKpos : 0≤highFactor (1/8) 14 ((3/4)*L) L := by unfold highFactor;positivity
  have hfull : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖≤
      (1001/1000:ℝ)*(2*exp (L/2)*(L^2+L))/L := by
    apply hk.trans
    apply div_le_div_of_nonneg_right _ hLp.le
    exact mul_le_mul (direct_factor_bound hL) hB' (Finset.sum_nonneg (fun q hq↦by
      have hw:=(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).1
      positivity)) (by norm_num)
  have he : exp (L/2)/exp L*exp (L/8)=exp (-(3/8:ℝ)*L) := by
    rw [←exp_sub,←exp_add]
    congr 1
    ring
  have hnorm : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖*
      (L/exp L)*exp (L/8)≤(1001/500:ℝ)*(L^2+L)*exp (-(3/8:ℝ)*L) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfull (by positivity : 0≤L/exp L)) (exp_pos _).le).trans_eq
    calc
      _ = (1001/500:ℝ)*(L^2+L)*(exp (L/2)/exp L*exp (L/8)) := by field_simp;ring
      _ = _ := by rw [he]
  have hquad:=DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 2
    (L0:=(300:ℝ)) (c:=3/8) (by norm_num) (by norm_num) hL
  have he75 : exp (-(3/8:ℝ)*300)≤1/(2:ℝ)^112 := by
    apply (exp_le_exp.mpr (by norm_num : -(3/8:ℝ)*300≤ -(112:ℝ))).trans
    exact DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 112
  have hsq : (L^2+L)*exp (-(3/8:ℝ)*L)≤180000/(2:ℝ)^112 := by
    have hx : L^2+L≤2*L^2 := by nlinarith
    have hexp : exp (-(3/8:ℝ)*L)≤exp (-(3/8:ℝ)*L) := exp_le_exp.mpr (by linarith)
    have hp:=mul_le_mul hx hexp (exp_pos _).le (by positivity : 0≤2*L^2)
    have he75' : exp (-(3/8:ℝ)*300)≤1/(2:ℝ)^112 := by convert he75 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he75' (by norm_num : (0:ℝ)≤(300:ℝ)^2)
    nlinarith
  apply hnorm.trans
  calc
    _ = (1001/500:ℝ)*((L^2+L)*exp (-(3/8:ℝ)*L)) := by ring
    _ ≤ (1001/500:ℝ)*(180000/(2:ℝ)^112) := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := by norm_num


theorem normalized_kernel (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) {L C : ℝ} (hL : 300 ≤ L)
    (hKernel : ‖∑q∈pairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ C) :
    Eπ (exp L)*exp (L/8) ≤ C+1/10000000000000 := by
  have h:=mul_le_mul_of_nonneg_right
    (actual_pi_from_CHJ_kernel (original_CHJ_to_paired hCHJ hqrh) hL) (exp_pos (L/8)).le
  have hTiny:=remainders hL
  change directRemainder L*exp (L/8) ≤ 1/10000000000000 at hTiny
  nlinarith


theorem rh_split_actual_pi_normalized (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C epsilon : ℝ} (hL : 300 ≤ L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C)
    (hLowKernel : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ epsilon) :
    Eπ (exp L)*exp (L/8) ≤ (1+33/10000000000000000)*C+epsilon+1/10000000000000 := by
  have hHigh:=high_kernel_normalized hqrh hlow hL hSpectral
  have hNorm:=norm_add_le
    (∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L)
    (∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L)
  rw [←split_paired_kernel] at hNorm
  have hLp : 0 < L := by linarith
  have hMult:=mul_le_mul_of_nonneg_right hNorm
    (by positivity : 0 ≤ (L/exp L)*exp (L/8))
  have hKernel : ‖∑q∈pairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
        (1+33/10000000000000000)*C+epsilon := by
    nlinarith only [hMult,hHigh,hLowKernel]
  exact normalized_kernel hCHJ hqrh hL hKernel

/-- Whole-ray adapter; both numerical and finite-RH providers are discharged
by the independently proved source lemmas in the final application. -/
theorem rh_pi_ray_of_budgets (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L0 C epsilon : ℝ} (hL0 : 300 ≤ L0)
    (hBudget : ∀L : ℝ,L0 ≤ L →
      WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C)
    (hLow : ∀L : ℝ,L0 ≤ L → ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ epsilon) :
    HasPowerLogBound Eπ ((1+33/10000000000000000)*C+epsilon+1/10000000000000) 0 (7/8) (exp L0) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L0).trans_le hx
  let L:=log x
  have hL : L0 ≤ L := by
    have hh:=log_le_log (exp_pos L0) hx
    simpa only [log_exp,L] using hh
  have heq : exp L=x := exp_log hx0
  have hh:=rh_split_actual_pi_normalized hCHJ hqrh hlow (hL0.trans hL)
    (hBudget L hL) (hLow L hL)
  rw [heq] at hh
  have hn : Eπ x ≤ ((1+33/10000000000000000)*C+epsilon+1/10000000000000)*exp (-L/8) := by
    have he : exp (-L/8)=1/exp (L/8) := by rw [show -L/8=-(L/8) by ring,exp_neg,one_div]
    rw [he,mul_one_div]
    exact (le_div_iff₀ (exp_pos _)).mpr hh
  simp only [pow_zero,mul_one]
  rw [rpow_def_of_pos hx0]
  have he : log x*((7/8:ℝ)-1)=-L/8 := by dsimp [L];ring
  rw [he]
  exact hn


#print axioms remainders
#print axioms rh_pi_ray_of_budgets
end PVEvolutionA.Tight
