/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongUConsumer
import Mathlib.MeasureTheory.Integral.DominatedConvergence
namespace WinnerStrongC4Source
open Real Set MeasureTheory
open WinnerOldFloors
set_option maxHeartbeats 0

theorem oldKernel_middle {u y : ℝ} (hu : h≤u) (hy : y∈Icc (-20:ℝ) 3) :
    oldKernel u y≤10000000 := by
  have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hr:=oldRatio_le_one hu
  have hr0:=oldRatio_nonneg hup
  have hz:=oldRzero_le_one hu
  have hz0 : 0≤oldRzero u := by unfold oldRzero a2 a1 a3;positivity
  have he1 : exp 1≤3 := exp_one_lt_three.le
  have he6 : exp 6≤729 := by
    have hp : (exp 1)^6≤(3:ℝ)^6 := by gcongr
    rw [←exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  have he3 : exp 3≤27 := by
    have hp : (exp 1)^3≤(3:ℝ)^3 := by gcongr
    rw [←exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp
  have hyabs : |y|≤20 := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hfac : |1+y/u|≤2 := by
    have hh:=abs_add_le (1:ℝ) (y/u)
    rw [abs_one,abs_div,abs_of_pos hup] at hh
    have hd : |y|/u≤(20:ℝ)/28 := div_le_div₀ (by norm_num : (0:ℝ)≤20) hyabs (by norm_num) hu28
    linarith
  have hexp : exp (y/6)≤3 :=
    (exp_le_exp.mpr (by linarith [hy.2] : y/6≤1)).trans he1
  have hAmp : |exp (y/6)*(1+y/u)+oldRzero u|≤7 := by
    calc _ ≤|exp (y/6)*(1+y/u)|+|oldRzero u| := abs_add_le _ _
         _ =exp (y/6)*|1+y/u|+oldRzero u := by rw [abs_mul,abs_of_pos (exp_pos _),abs_of_nonneg hz0]
         _ ≤3*2+1 := by gcongr
         _ =_ := by norm_num
  have hsq : (exp (y/6)*(1+y/u)+oldRzero u)^2≤49 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hAmp 2
    norm_num only [sq_abs] at hh
    exact hh
  have hweight : exp (2*y-2*alpha*exp (2*y))≤729 := by
    apply le_trans _ he6
    apply exp_le_exp.mpr
    unfold alpha
    nlinarith [hy.2,exp_pos (2*y)]
  have hfac2 : exp y+oldRatio u≤28 := by
    have hey : exp y≤27 := (exp_le_exp.mpr hy.2).trans he3
    linarith
  unfold oldKernel
  have hp := mul_le_mul hweight hsq (sq_nonneg _) (by norm_num : (0:ℝ)≤729)
  have hp2 := mul_le_mul hp hfac2 (by positivity : 0≤exp y+oldRatio u) (by norm_num : (0:ℝ)≤729*49)
  norm_num at hp2 ⊢
  linarith

noncomputable def dominating (y : ℝ) : ℝ :=
  (Iic (-20:ℝ)).indicator (fun y=>8*exp y) y+
    (Ioc (-20:ℝ) 3).indicator (fun _=>10000000) y+
      (Ioi (3:ℝ)).indicator (fun y=>8*exp (-y-20)) y

theorem dominating_integrable : Integrable dominating := by
  have hl : IntegrableOn (fun y : ℝ=>8*exp y) (Iic (-20)) :=
    (integrableOn_exp_Iic (-20)).const_mul _
  have hm : IntegrableOn (fun _ : ℝ=>(10000000:ℝ)) (Ioc (-20) 3) :=
    (continuous_const.intervalIntegrable (-20) 3).1
  have hh : IntegrableOn (fun y : ℝ=>8*exp (-y-20)) (Ioi 3) := by
    have he : (fun y : ℝ=>8*exp (-y-20))=fun y=>(8*exp (-20))*exp (-y) := by
      funext y
      rw [show -y-20=(-20)+(-y) by ring,exp_add]
      ring
    rw [he]
    exact (integrableOn_exp_neg_Ioi 3).const_mul _
  unfold dominating
  exact ((hl.integrable_indicator measurableSet_Iic).add
    (hm.integrable_indicator measurableSet_Ioc)).add (hh.integrable_indicator measurableSet_Ioi)

theorem oldKernel_dominated {u : ℝ} (hu : h≤u) (y : ℝ) : ‖oldKernel u y‖≤dominating y := by
  rw [Real.norm_eq_abs,abs_of_nonneg (oldKernel_nonneg hu)]
  by_cases hlo : y≤-20
  · have hmid : ¬(-20:ℝ)<y := by linarith
    have hhi : ¬3<y := by linarith
    have he : dominating y=8*exp y := by simp [dominating,Set.indicator,hlo,hmid,hhi]
    rw [he]
    exact oldKernel_low hu hlo
  · have hlo' : -20<y := lt_of_not_ge hlo
    by_cases hhi : 3<y
    · have hmid : ¬y≤3 := by linarith
      have he : dominating y=8*exp (-y-20) := by simp [dominating,Set.indicator,hlo,hhi,hmid]
      rw [he]
      exact oldKernel_high hu hhi.le
    · have hmid : y≤3 := le_of_not_gt hhi
      have he : dominating y=10000000 := by simp [dominating,Set.indicator,hlo,hlo',hhi,hmid]
      rw [he]
      exact oldKernel_middle hu ⟨hlo'.le,hmid⟩

theorem oldKernel_parameter_continuous (y : ℝ) : ContinuousOn (fun u=>oldKernel u y) (Ici h) := by
  intro u hu
  have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
  have hu0 : u≠0 := hup.ne'
  have hm : mone u≠0 := (mone_pos hup).ne'
  have hd : a1*exp (u/6)*u≠0 := by unfold a1;positivity
  apply ContinuousAt.continuousWithinAt
  unfold oldKernel oldRzero oldRatio mtwo mone
  fun_prop (disch := first | assumption | positivity)

theorem oldU_continuousOn : ContinuousOn oldU (Ici h) := by
  have hint : ContinuousOn (fun u=>∫ y : ℝ,oldKernel u y) (Ici h) := by
    apply continuousOn_of_dominated (bound:=dominating)
    · intro u hu
      exact (oldKernel_continuous u).aestronglyMeasurable
    · intro u hu
      exact Filter.Eventually.of_forall (oldKernel_dominated hu)
    · exact dominating_integrable
    · exact Filter.Eventually.of_forall oldKernel_parameter_continuous
  have hpref : ContinuousOn (fun u=>8*alpha*oldC4 u*exp (alpha/(2*exp (2*u)))) (Ici h) := by
    intro u hu
    have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
    have hu0 : u≠0 := hup.ne'
    have hsqrt : sqrt u≠0 := (sqrt_pos.mpr hup).ne'
    apply ContinuousAt.continuousWithinAt
    unfold oldC4 mone a1 a3
    fun_prop (disch := first | assumption | positivity)
  exact hpref.mul hint

#print axioms oldU_continuousOn
end WinnerStrongC4Source
