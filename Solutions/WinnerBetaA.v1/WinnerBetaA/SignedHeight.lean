/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerBetaA.HeightSource
namespace WinnerBetaA.SignedHeight
open Real Set MeasureTheory
open WinnerBetaA.Minkowski WinnerBetaA.ActualObject WinnerBetaA.HeightSource
set_option maxHeartbeats 0

noncomputable def bracket (a1 a2 m1 m2 A x : ℝ) : ℝ :=
  sqrt (m1*x+m2)*(x^((1:ℝ)/6)*(1+max (log x) 0/log A)+a2/(a1*A^((1:ℝ)/6)*log A))+
    (1/(a1*A^((1:ℝ)/6)*log A*sqrt (log A)))*sqrt x
noncomputable def kernel (M1 M2 h r0 r1 y : ℝ) : ℝ :=
  exp (2*y-(601/2500:ℝ)*exp (2*y))*
    (sqrt (M1*exp y+M2)*(exp (y/6)*(1+max y 0/h)+r0)+r1*exp (y/2))^2

theorem factor_bound {a1 a2 A T x : ℝ} (ha1 : 0<a1) (ha2 : 0≤a2)
    (hA : 1<A) (hAT : A≤T) (hx : 0<x) :
    (a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2)/(a1*T^((1:ℝ)/6)*log T)≤
      x^((1:ℝ)/6)*(1+max (log x) 0/log A)+a2/(a1*A^((1:ℝ)/6)*log A) := by
  have hT : 1<T := hA.trans_le hAT
  have hAp : 0<A := by linarith
  have hTp : 0<T := by linarith
  have hlA := log_pos hA
  have hlT := log_pos hT
  have hlAT := log_le_log hAp hAT
  have hpA : 0<A^((1:ℝ)/6) := rpow_pos_of_pos hAp _
  have hpT : 0<T^((1:ℝ)/6) := rpow_pos_of_pos hTp _
  have hdenA : 0<a1*A^((1:ℝ)/6)*log A := by positivity
  have hden : a1*A^((1:ℝ)/6)*log A≤a1*T^((1:ℝ)/6)*log T := by gcongr
  have hr0 := div_le_div_of_nonneg_left ha2 hdenA hden
  have hlog : log x/log T≤max (log x) 0/log A := by
    apply (div_le_div_of_nonneg_right (le_max_left (log x) 0) hlT.le).trans
    exact div_le_div_of_nonneg_left (le_max_right (log x) 0) hlA hlAT
  have he : (a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2)/(a1*T^((1:ℝ)/6)*log T)=
      x^((1:ℝ)/6)*(1+log x/log T)+a2/(a1*T^((1:ℝ)/6)*log T) := by
    rw [mul_rpow hx.le hTp.le,log_mul hx.ne' hTp.ne']
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hlog (rpow_pos_of_pos hx ((1:ℝ)/6)).le
  nlinarith

theorem amplitude_bound {a1 a2 m1 m2 A T x low : ℝ}
    (ha1 : 0<a1) (ha2 : 0≤a2) (hm1 : 0≤m1) (hm2 : 0≤m2)
    (hlow : 0≤low) (hFloor : 6*a1/exp 1+low≤a2)
    (hA : 1<A) (hAT : A≤T) (hx : 0<x) :
    0≤rawAmplitude a1 a2 m1 m2 T x ∧
      rawAmplitude a1 a2 m1 m2 T x/(a1*normalizationScale T)≤bracket a1 a2 m1 m2 A x := by
  have hT : 1<T := hA.trans_le hAT
  have hTp : 0<T := by linarith
  have hlT := log_pos hT
  have hxp : 0<x*T := mul_pos hx hTp
  have hfac : low≤a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2 := by
    linear_combination a1*(power_log_minimum hxp)+hFloor
  have hfac0 := hlow.trans hfac
  have hraw0 : 0≤rawAmplitude a1 a2 m1 m2 T x := by unfold rawAmplitude;positivity
  refine ⟨hraw0,?_⟩
  have hD : 0≤m1*x+m2 := by positivity
  have hroot : sqrt ((m1*x*T+m2*T)*log T)=sqrt (m1*x+m2)*sqrt T*sqrt (log T) := by
    rw [show (m1*x*T+m2*T)*log T=((m1*x+m2)*T)*log T by ring,
      sqrt_mul (mul_nonneg hD hTp.le),sqrt_mul hD]
  have he : rawAmplitude a1 a2 m1 m2 T x/(a1*normalizationScale T)=
      sqrt (m1*x+m2)*((a1*(x*T)^((1:ℝ)/6)*log (x*T)+a2)/(a1*T^((1:ℝ)/6)*log T))+
        (1/(a1*T^((1:ℝ)/6)*log T*sqrt (log T)))*sqrt x := by
    unfold rawAmplitude
    rw [hroot,sqrt_mul hx.le]
    unfold normalizationScale
    field_simp
  rw [he]
  have h1 := mul_le_mul_of_nonneg_left (factor_bound ha1 ha2 hA hAT hx) (sqrt_nonneg (m1*x+m2))
  have h2 := mul_le_mul_of_nonneg_right (residual_bound ha1 hA hAT) (sqrt_nonneg x)
  unfold bracket
  linarith

theorem normalized_raw {a1 a2 m1 m2 A T x low : ℝ}
    (ha1 : 0<a1) (ha2 : 0≤a2) (hm1 : 0≤m1) (hm2 : 0≤m2)
    (hlow : 0≤low) (hFloor : 6*a1/exp 1+low≤a2)
    (hA : 1<A) (hAT : A≤T) (hx : 0<x) :
    rawAmplitude a1 a2 m1 m2 T x^2/(log T^3*T^((4:ℝ)/3))≤
      a1^2*bracket a1 a2 m1 m2 A x^2 := by
  have hT : 1<T := hA.trans_le hAT
  have hTp : 0<T := by linarith
  have hlT := log_pos hT
  have hs : 0<normalizationScale T := by unfold normalizationScale;positivity
  have hden : 0<log T^3*T^((4:ℝ)/3) := by positivity
  obtain ⟨hraw0,hamp⟩ := amplitude_bound ha1 ha2 hm1 hm2 hlow hFloor hA hAT hx
  have hp := pow_le_pow_left₀ (show 0≤rawAmplitude a1 a2 m1 m2 T x/(a1*normalizationScale T) by positivity) hamp 2
  rw [div_pow,mul_pow,normalizationScale_sq hT] at hp
  have hb := (div_le_iff₀ (mul_pos (sq_pos_of_pos ha1) hden)).mp hp
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem bracket_majorized {a1 a2 m1 m2 A M1 M2 h r0 r1 x : ℝ}
    (ha1 : 0<a1) (ha2 : 0≤a2) (hA : 1<A) (hx : 0<x)
    (hm1 : m1≤M1) (hm2 : m2≤M2) (hh : 0<h) (hhA : h≤log A)
    (hr0 : a2/(a1*A^((1:ℝ)/6)*log A)≤r0)
    (hr1 : 1/(a1*A^((1:ℝ)/6)*log A*sqrt (log A))≤r1) :
    bracket a1 a2 m1 m2 A x ≤ sqrt (M1*x+M2)*(x^((1:ℝ)/6)*(1+max (log x) 0/h)+r0)+r1*sqrt x := by
  have hlA := log_pos hA
  have hAp : 0<A := by linarith
  have hroot : sqrt (m1*x+m2)≤sqrt (M1*x+M2) := by
    apply sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_right hm1 hx.le]
  have hratio := div_le_div_of_nonneg_left (le_max_right (log x) 0) hh hhA
  have hxp : 0≤x^((1:ℝ)/6) := (rpow_pos_of_pos hx _).le
  have hinner : x^((1:ℝ)/6)*(1+max (log x) 0/log A)+a2/(a1*A^((1:ℝ)/6)*log A)≤
      x^((1:ℝ)/6)*(1+max (log x) 0/h)+r0 := by
    nlinarith [mul_le_mul_of_nonneg_left hratio hxp]
  have hinner0 : 0≤x^((1:ℝ)/6)*(1+max (log x) 0/log A)+a2/(a1*A^((1:ℝ)/6)*log A) := by positivity
  have hprod := mul_le_mul hroot hinner hinner0 (sqrt_nonneg (M1*x+M2))
  have hres := mul_le_mul_of_nonneg_right hr1 (sqrt_nonneg x)
  unfold bracket
  linarith

#print axioms normalized_raw
#print axioms bracket_majorized
end WinnerBetaA.SignedHeight
