/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldIntegrability
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors WinnerOldAnalytic
set_option maxHeartbeats 0

theorem oldU_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    truncatedOldU v≤oldU u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hc:=oldKernel_continuous u
  have hi:=oldKernel_integrable hlu
  have hneg : (∫ y in (-3:ℝ)..0,kernel alpha h (ratioFloor v) y)≤
      ∫ y in (-3:ℝ)..0,oldKernel u y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((kernel_continuous alpha h (ratioFloor v)).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro y hy
    have h:=oldKernel_lower hv hlu hur ⟨hy.1,by linarith [hy.2]⟩
    simpa only [if_pos hy.2] using h
  have hpos : (∫ y in (0:ℝ)..3,kernel alpha (h+v) (ratioFloor v) y)≤
      ∫ y in (0:ℝ)..3,oldKernel u y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((kernel_continuous alpha (h+v) (ratioFloor v)).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    intro y hy
    have h:=oldKernel_lower hv hlu hur ⟨by linarith [hy.1],hy.2⟩
    by_cases hy0 : y≤0
    · have hey : y=0 := by linarith [hy.1]
      subst y
      simpa only [kernel,zero_div,add_zero,mul_zero,zero_sub,exp_zero,zero_add,
        one_mul,div_zero,zero_mul,one_pow] using h
    · simpa only [if_neg hy0] using h
  have hsum := add_le_add hneg hpos
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-3) 0) (hc.intervalIntegrable 0 3)] at hsum
  have hfull : (∫ y in (-3:ℝ)..3,oldKernel u y)≤∫ y : ℝ,oldKernel u y := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun y=>oldKernel_nonneg hlu))
  have hpartial:=hsum.trans hfull
  have hpref : 0≤8*alpha*c4Floor v := by unfold alpha;positivity [c4_nonneg v]
  have hp:=mul_le_mul_of_nonneg_left hpartial hpref
  have htot : 0≤∫ y : ℝ,oldKernel u y := integral_nonneg (by intro y;exact oldKernel_nonneg hlu)
  have hc4:=oldC4_lower hv hlu hur
  have hexp : 1≤exp (alpha/(2*exp (2*u))) := by
    apply one_le_exp
    unfold alpha
    positivity
  have hpref : 8*alpha*c4Floor v≤8*alpha*oldC4 u*exp (alpha/(2*exp (2*u))) := by
    have h1:=mul_le_mul_of_nonneg_left hc4 (by norm_num [alpha] : 0≤8*alpha)
    have h2:=mul_le_mul_of_nonneg_left hexp
      (by unfold oldC4 alpha;positivity : 0≤8*alpha*oldC4 u)
    nlinarith
  unfold truncatedOldU oldU
  change 8*alpha*c4Floor v*((∫ y in (-3:ℝ)..0,kernel alpha h (ratioFloor v) y)+
      (∫ y in (0:ℝ)..3,kernel alpha (h+v) (ratioFloor v) y))≤_
  exact hp.trans (mul_le_mul_of_nonneg_right hpref htot)

theorem oldU_one {u : ℝ} (hu : h≤u) (hu' : u≤h+1) :
    (1698779/1000000:ℝ)≤oldU u :=
  oldU_floor1.trans (oldU_floor (by norm_num) hu hu')
theorem oldU_two {u : ℝ} (hu : h≤u) (hu' : u≤h+2) :
    (1682465/1000000:ℝ)≤oldU u :=
  oldU_floor2.trans (oldU_floor (by norm_num) hu hu')
theorem oldU_four {u : ℝ} (hu : h≤u) (hu' : u≤h+4) :
    (1652763/1000000:ℝ)≤oldU u :=
  oldU_floor4.trans (oldU_floor (by norm_num) hu hu')
theorem oldU_eight {u : ℝ} (hu : h≤u) (hu' : u≤h+8) :
    (1602809/1000000:ℝ)≤oldU u :=
  oldU_floor8.trans (oldU_floor (by norm_num) hu hu')

#print axioms oldU_floor
#print axioms oldU_eight
end WinnerOldC4Source
