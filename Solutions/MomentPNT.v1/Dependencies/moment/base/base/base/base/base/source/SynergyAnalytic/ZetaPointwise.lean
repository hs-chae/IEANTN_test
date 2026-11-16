import WinnerBetaA.ActualObject
import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerBetaA.ActualObject
set_option maxHeartbeats 0

noncomputable def zetaScale (T : ℝ) : ℝ := (611/1000:ℝ)*T^((1:ℝ)/6)*Real.log T
noncomputable def zetaShape (h x : ℝ) : ℝ :=
  x^((1:ℝ)/6)*(1+max (Real.log x) 0/h)

theorem zetaShape_nonneg {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) : 0 ≤ zetaShape h x := by
  have hl : 0 ≤ max (Real.log x) 0 := le_max_right _ _
  unfold zetaShape
  positivity

/-- A direct low/high split avoids the old global amplitude-floor numerical
check.  It uses precisely the two original zeta bounds, not a new zeta estimate. -/
theorem zeta_pointwise_source
    {T h r x : ℝ} (hT : 1 < T) (hh : 0 < h) (hhT : h ≤ Real.log T) (hx : 0 < x)
    (hr : (1461/1000:ℝ)/zetaScale T ≤ r)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 → ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHigh : ∀ u : ℝ, 3 ≤ u → ‖riemannZeta (vertical (1/2) u)‖ ≤
      (611/1000:ℝ)*u^((1:ℝ)/6)*Real.log u) :
    ‖riemannZeta (vertical (1/2) (x*T))‖ ≤ zetaScale T*(zetaShape h x+r) := by
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hamp : 0 < zetaScale T := by unfold zetaScale;positivity
  have hrp : 0 ≤ r := (div_nonneg (by norm_num) hamp.le).trans hr
  have hsr : (1461/1000:ℝ) ≤ zetaScale T*r := by
    have hn := (div_le_iff₀ hamp).mp hr
    nlinarith
  by_cases hsmall : x*T ≤ 3
  · have hl := hLow (x*T) (mul_pos hx hTp).le hsmall
    have hs := zetaShape_nonneg hh hx.le
    nlinarith
  · have hu : 3 ≤ x*T := le_of_not_ge hsmall
    have hz := hHigh (x*T) hu
    have hlp : 0 ≤ max (Real.log x) 0 := le_max_right _ _
    have hl1 : Real.log x/Real.log T ≤ max (Real.log x) 0/Real.log T :=
      div_le_div_of_nonneg_right (le_max_left _ _) hlog.le
    have hl2 : max (Real.log x) 0/Real.log T ≤ max (Real.log x) 0/h :=
      div_le_div_of_nonneg_left hlp hh hhT
    have hl : Real.log (x*T) ≤ Real.log T*(1+max (Real.log x) 0/h) := by
      rw [Real.log_mul hx.ne' hTp.ne']
      have hi := (div_le_iff₀ hlog).mp (hl1.trans hl2)
      nlinarith
    have hb := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ (611/1000:ℝ)*(x*T)^((1:ℝ)/6) by positivity)
    rw [Real.mul_rpow hx.le hTp.le] at hb
    have hz' : (611/1000:ℝ)*(x*T)^((1:ℝ)/6)*Real.log (x*T) ≤ zetaScale T*zetaShape h x := by
      rw [Real.mul_rpow hx.le hTp.le]
      convert hb using 1 <;> first | rfl | (unfold zetaScale zetaShape;ring)
    have hs := mul_nonneg hamp.le hrp
    exact (hz.trans hz').trans (by nlinarith)

#print axioms zeta_pointwise_source
end SynergyAnalytic
