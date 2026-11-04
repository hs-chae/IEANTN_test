/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldC4Source
import StrongIntegrability
import StrongMomentConsumer
namespace WinnerStrongC4Source
open Real Set MeasureTheory WinnerOldFloors
set_option maxHeartbeats 0
noncomputable def floorU (v : ℝ) : ℝ :=
  8*alpha*oldC4 (h+v)*WinnerStrongC4.expanded WinnerStrongC4.momentLower
    (h+v) (ratioFloor v) (oldRzero (h+v))

theorem c4_antitone {u ur : ℝ} (hu : 0<u) (hur : u≤ur) : oldC4 ur≤oldC4 u := by
  have hup : 0<ur := hu.trans_le hur
  have hm : mone ur≤mone u := by unfold mone;gcongr
  have hs:=sqrt_le_sqrt hm
  have hrec : 1/(a3*sqrt ur)≤1/(a3*sqrt u) := by
    apply one_div_le_one_div_of_le (by unfold a3;positivity)
    unfold a3
    gcongr
  have hsum : sqrt (mone ur)+1/(a3*sqrt ur)≤sqrt (mone u)+1/(a3*sqrt u) := by linarith
  unfold oldC4
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold a3;positivity) hsum 2) (by unfold a1;positivity)

theorem rzero_antitone {u ur : ℝ} (hu : 0<u) (hur : u≤ur) : oldRzero ur≤oldRzero u := by
  have hup : 0<ur := hu.trans_le hur
  unfold oldRzero
  apply div_le_div_of_nonneg_left (by unfold a2 a1 a3;positivity) (by unfold a1;positivity)
  unfold a1
  gcongr

theorem ratio_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    ratioFloor v≤oldRatio u := by
  simpa only [oldRatio,mtwo,mone,mzero,WinnerOldC4Source.oldRatio,
    WinnerOldC4Source.mtwo,WinnerOldC4Source.mone,WinnerOldC4Source.mzero]
    using WinnerOldC4Source.oldRatio_lower hv hlu hur

theorem oldU_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) : floorU v≤oldU u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hurp : 0<h+v := by positivity
  have hr:=oldRatio_nonneg hup
  have hz : 0≤oldRzero u := by unfold oldRzero a2 a1 a3;positivity
  have hz' : 0≤oldRzero (h+v) := by unfold oldRzero a2 a1 a3;positivity
  have hm:=WinnerStrongC4.expanded_parameters
    (j:=WinnerStrongC4.momentLower) (fun i _=>WinnerStrongC4.moment_lower_nonneg i)
    hup hur (ratio_nonneg hv) (ratio_floor hv hlu hur) hz' (rzero_antitone hup hur)
  have hk:=WinnerStrongC4.checked_finite_kernel_lower hup hr hz
  have hk' : WinnerStrongC4.expanded WinnerStrongC4.momentLower u (oldRatio u) (oldRzero u)≤
      ∫y in (-12:ℝ)..3,oldKernel u y := by
    convert! hk using 1
  have hi:=oldKernel_integrable hlu
  have hnn : 0≤∫y in (-12:ℝ)..3,oldKernel u y :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun y=>oldKernel_nonneg hlu)
  have hrestrict : (∫y in (-12:ℝ)..3,oldKernel u y)≤∫y:ℝ,oldKernel u y := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _=>oldKernel_nonneg hlu))
  have hc4 : 0≤oldC4 (h+v) := by unfold oldC4;positivity
  have hcf:=c4_antitone hup hur
  have hmpos : 0≤WinnerStrongC4.expanded WinnerStrongC4.momentLower (h+v)
      (ratioFloor v) (oldRzero (h+v)) := by
    have hn:=WinnerStrongC4.expanded_mono (j:=fun _=>0) hurp (ratio_nonneg hv) hz'
      (fun i _=>WinnerStrongC4.moment_lower_nonneg i)
    simpa only [WinnerStrongC4.expanded,mul_zero,add_zero,zero_add] using hn
  have hintegral : 0≤∫y:ℝ,oldKernel u y := integral_nonneg (fun y=>oldKernel_nonneg hlu)
  have hpre : floorU v≤8*alpha*oldC4 u*(∫y:ℝ,oldKernel u y) := by
    unfold floorU
    have hn:=hm.trans (hk'.trans hrestrict)
    have hc:=mul_le_mul_of_nonneg_left hcf (by norm_num [alpha] : 0≤8*alpha)
    exact mul_le_mul hc hn hmpos (by unfold oldC4 alpha;positivity)
  have he : 1≤exp (alpha/(2*exp (2*u))) := by apply one_le_exp;unfold alpha;positivity
  have hpref : 8*alpha*oldC4 u≤8*alpha*oldC4 u*exp (alpha/(2*exp (2*u))) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (by unfold oldC4 alpha;positivity : 0≤8*alpha*oldC4 u)
  exact hpre.trans (mul_le_mul_of_nonneg_right hpref hintegral)

#print axioms oldU_floor
end WinnerStrongC4Source
