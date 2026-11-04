/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
namespace WinnerStrongC4Source
open Real Set MeasureTheory
open WinnerOldFloors
set_option maxHeartbeats 0

theorem mzero_le_two : mzero≤2 := by
  have hs : sqrt (6/5:ℝ)≤2 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
  unfold mzero
  apply (sqrt_le_left (by norm_num)).mpr
  nlinarith

theorem oldRatio_le_one {u : ℝ} (hu : h≤u) : oldRatio u≤1 := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hup : 0<u := by linarith
  have hm0:=mzero_pos
  have hm:=mzero_le_two
  have hpi : (3:ℝ)≤Real.pi := pi_gt_three.le
  have hpi' : Real.pi≤4 := pi_lt_four.le
  have he : exp (-u)≤1/29 := by
    have hh:=add_one_le_exp u
    have h29 : (29:ℝ)≤exp u := by linarith
    have hi:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<29) h29
    simpa [exp_neg,one_div] using hi
  have h1 : Real.pi*mzero*(31/50)/u≤(4:ℝ)*2*(31/50)/28 := by gcongr
  have h2 : 6*mzero/Real.pi*exp (-u)≤(6:ℝ)*2/3*(1/29) := by gcongr
  have h3 : Real.pi*mzero*(131/125)*exp (-u)/u≤(4:ℝ)*2*(131/125)*(1/29)/28 := by gcongr
  have htwo : mtwo u≤(1/3:ℝ) := by unfold mtwo;linarith
  have hone : (3/8:ℝ)≤mone u := by
    have hp2 : Real.pi^2≤16 := by nlinarith [Real.pi_pos]
    have hh : (6:ℝ)/16≤6/Real.pi^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hp2
    have hb : 0≤(131/125:ℝ)/u := by positivity
    unfold mone
    linarith
  unfold oldRatio
  apply (div_le_one (mone_pos hup)).mpr
  linarith

theorem oldRzero_le_one {u : ℝ} (hu : h≤u) : oldRzero u≤1 := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hup : 0<u := by linarith
  have he1 : (1:ℝ)≤exp 1 := one_le_exp_iff.mpr (by norm_num)
  have ha2 : a2≤6*a1+a3 := by
    unfold a2
    have hh : 6*a1/exp 1≤6*a1 := by
      apply (div_le_iff₀ (exp_pos _)).mpr
      have hh:=mul_le_mul_of_nonneg_left he1 (by norm_num [a1] : 0≤6*a1)
      simpa using hh
    linarith
  have hexp : (17/3:ℝ)≤exp (u/6) := by
    have he:=add_one_le_exp (u/6)
    linarith
  have hden : 6*a1+a3≤a1*exp (u/6)*u := by
    have hh:=mul_le_mul_of_nonneg_left hexp (by norm_num [a1] : 0≤a1)
    have hp:=mul_le_mul hh hu28 (by norm_num) (by unfold a1;positivity)
    norm_num [a1,a3] at hp ⊢
    linarith
  unfold oldRzero
  apply (div_le_one (by unfold a1;positivity)).mpr
  exact ha2.trans hden


theorem oldKernel_nonneg {u y : ℝ} (hu : h≤u) : 0≤oldKernel u y := by
  have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
  have hr:=oldRatio_nonneg hup
  unfold oldKernel
  positivity

theorem oldKernel_continuous (u : ℝ) : Continuous (oldKernel u) := by unfold oldKernel;fun_prop

theorem oldKernel_low {u y : ℝ} (hu : h≤u) (hy : y≤-20) : oldKernel u y≤8*exp y := by
  have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hy0 : y≤0 := by linarith
  have hr:=oldRatio_le_one hu
  have hr0:=oldRatio_nonneg hup
  have hz:=oldRzero_le_one hu
  have hz0 : 0≤oldRzero u := by unfold oldRzero a2 a1 a3;positivity
  have hey : exp y≤1 := exp_le_one_iff.mpr hy0
  have he6 : exp (y/6)≤1 := exp_le_one_iff.mpr (by linarith)
  have ha : |1+y/u|≤1+(-y)/28 := by
    have hab:=abs_add_le (1:ℝ) (y/u)
    rw [abs_one,abs_div,abs_of_pos hup,abs_of_nonpos hy0] at hab
    have hdiv : (-y)/u≤(-y)/28 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hu28
    linarith
  have hb : |exp (y/6)*(1+y/u)+oldRzero u|≤-y := by
    calc
      _ ≤ |exp (y/6)*(1+y/u)|+|oldRzero u| := abs_add_le _ _
      _ = exp (y/6)*|1+y/u|+oldRzero u := by rw [abs_mul,abs_of_pos (exp_pos _),abs_of_nonneg hz0]
      _ ≤ 1*(1+(-y)/28)+1 := by gcongr
      _ ≤ _ := by linarith
  have hsq : (exp (y/6)*(1+y/u)+oldRzero u)^2≤y^2 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hb 2
    simpa only [sq_abs,neg_sq] using hh
  have hweight : exp (2*y-2*alpha*exp (2*y))≤exp (2*y) := by
    apply exp_le_exp.mpr
    unfold alpha
    nlinarith [exp_pos (2*y)]
  have hfirst : oldKernel u y≤2*exp (2*y)*y^2 := by
    unfold oldKernel
    calc
      _ ≤ exp (2*y)*y^2*(1+1) := by gcongr
      _ = _ := by ring
  have hs := add_one_le_exp ((-y)/2)
  have hexpsq : exp ((-y)/2)^2=exp (-y) := by rw [pow_two,←exp_add];congr 1;ring
  have hss : ((-y)/2)^2≤exp ((-y)/2)^2 := by gcongr <;> linarith
  rw [hexpsq] at hss
  have hysq : y^2≤4*exp (-y) := by nlinarith
  calc oldKernel u y ≤2*exp (2*y)*y^2 := hfirst
       _ ≤2*exp (2*y)*(4*exp (-y)) := by gcongr
       _ =8*exp y := by
         rw [show 2*exp (2*y)*(4*exp (-y))=8*(exp (2*y)*exp (-y)) by ring,←exp_add]
         congr 2
         ring

theorem exp_six_lower : (200:ℝ)≤exp 6 := by
  have he : (5/2:ℝ)≤exp 1 := by linarith [exp_one_gt_d9]
  have hp : (5/2:ℝ)^6≤(exp 1)^6 := by gcongr
  have hh : exp 6=(exp 1)^6 := by simpa using exp_nat_mul (1:ℝ) 6
  rw [←hh] at hp
  norm_num at hp ⊢
  linarith

theorem oldKernel_high {u y : ℝ} (hu : h≤u) (hy : 3≤y) : oldKernel u y≤8*exp (-y-20) := by
  have hup : 0<u := lt_of_lt_of_le (by linarith [h_lower]) hu
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hy0 : 0≤y := by linarith
  have hr:=oldRatio_le_one hu
  have hr0:=oldRatio_nonneg hup
  have hz:=oldRzero_le_one hu
  have hz0 : 0≤oldRzero u := by unfold oldRzero a2 a1 a3;positivity
  have hey : 1≤exp y := one_le_exp_iff.mpr hy0
  have hlog : 1+y/u≤exp (y/28) := by
    have hdiv : y/u≤y/28 := div_le_div_of_nonneg_left hy0 (by norm_num) hu28
    have he:=add_one_le_exp (y/28)
    linarith
  have hp : exp (y/6)*(1+y/u)≤exp (y/4) := by
    calc _ ≤exp (y/6)*exp (y/28) := by gcongr
         _ =exp (y/6+y/28) := (exp_add _ _).symm
         _ ≤_ := exp_le_exp.mpr (by linarith)
  have hq : 1≤exp (y/4) := one_le_exp_iff.mpr (by linarith)
  have hA0 : 0≤exp (y/6)*(1+y/u)+oldRzero u := by positivity
  have hA : exp (y/6)*(1+y/u)+oldRzero u≤2*exp (y/4) := by linarith
  have hsq : (exp (y/6)*(1+y/u)+oldRzero u)^2≤4*exp (y/2) := by
    have hh:=pow_le_pow_left₀ hA0 hA 2
    have he : exp (y/4)^2=exp (y/2) := by rw [pow_two,←exp_add];congr 1;ring
    nlinarith
  have hrExp : oldRatio u≤exp y := hr.trans hey
  have hfirst : oldKernel u y≤8*exp ((7/2)*y-2*alpha*exp (2*y)) := by
    unfold oldKernel
    calc
      _ ≤exp (2*y-2*alpha*exp (2*y))*(4*exp (y/2))*(exp y+exp y) := by gcongr
      _ =_ := by
        rw [show exp (2*y-2*alpha*exp (2*y))*(4*exp (y/2))*(exp y+exp y)=
          8*(exp (2*y-2*alpha*exp (2*y))*exp (y/2)*exp y) by ring,←exp_add,←exp_add]
        congr 2
        ring
  have ht:=add_one_le_exp (2*(y-3))
  have hexp : exp (2*y)=exp 6*exp (2*(y-3)) := by rw [←exp_add];congr 1;ring
  have hdom : (9/2:ℝ)*y+20≤2*alpha*exp (2*y) := by
    rw [hexp]
    have he:=mul_le_mul exp_six_lower ht (by linarith : 0≤2*(y-3)+1) (exp_pos 6).le
    unfold alpha
    nlinarith
  exact hfirst.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num))

theorem oldKernel_integrable {u : ℝ} (hu : h≤u) : Integrable (oldKernel u) := by
  have hc:=oldKernel_continuous u
  have hl : IntegrableOn (oldKernel u) (Iic (-20)) := by
    apply ((integrableOn_exp_Iic (-20)).const_mul (8:ℝ)).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (oldKernel_nonneg hu)]
    exact oldKernel_low hu hy
  have hh : IntegrableOn (oldKernel u) (Ioi 3) := by
    have hi:= (integrableOn_exp_neg_Ioi 3).const_mul ((8:ℝ)*exp (-20))
    apply hi.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (oldKernel_nonneg hu)]
    have h:=oldKernel_high hu hy.le
    convert! h using 1
    rw [show -y-20=(-20)+(-y) by ring,exp_add]
    ring
  have hm : IntegrableOn (oldKernel u) (Ioc (-20) 3) := (hc.intervalIntegrable (-20) 3).1
  have hu1:=hl.union hm
  have he : Iic (-20:ℝ)∪Ioc (-20) 3=Iic 3 := by ext y;simp;constructor <;> intro hy <;> grind
  rw [he] at hu1
  have hall:=hu1.union hh
  rw [Iic_union_Ioi,integrableOn_univ] at hall
  exact hall

#print axioms oldRatio_le_one
#print axioms oldRzero_le_one
#print axioms oldKernel_integrable
end WinnerStrongC4Source
