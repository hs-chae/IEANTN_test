import SynergyAnalytic.Cumulative
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem gaussian_area_bound {q b : ℝ} (hq : 0 < q) :
    (∫ x in (0:ℝ)..b, Real.exp (-q*x^2)) ≤ Real.sqrt (Real.pi/q)/2 := by
  have hi := integrable_exp_neg_mul_sq hq
  have he := intervalIntegral.integral_interval_add_Ioi
    (hi.integrableOn (s:=Ioi (0:ℝ))) (hi.integrableOn (s:=Ioi b))
  have hn : 0 ≤ (∫ x in Ioi b, Real.exp (-q*x^2)) :=
    setIntegral_nonneg measurableSet_Ioi (by intro x hx;positivity)
  rw [integral_gaussian_Ioi q] at he
  linarith

theorem gaussian_cumulative_cap
    {F f : ℝ → ℝ} {q b m c : ℝ} (hq : 0 < q) (hb : 0 ≤ b)
    (hF : ContinuousOn F (Icc 0 b)) (hf : ContinuousOn f (Icc 0 b))
    (hFd : ∀ x ∈ Ioo 0 b, HasDerivAt F (f x) x) (hF0 : F 0 = 0)
    (hcap : ∀ x ∈ Icc 0 b, F x ≤ m*x+c) :
    (∫ x in (0:ℝ)..b, Real.exp (-q*x^2)*f x) ≤
      m*(∫ x in (0:ℝ)..b, Real.exp (-q*x^2))+c := by
  have hw : Continuous (fun x : ℝ => Real.exp (-q*x^2)) := by fun_prop
  have hwp : Continuous (fun x : ℝ => Real.exp (-q*x^2)*(-q*(2*x))) := by fun_prop
  have hd : ∀ x : ℝ, HasDerivAt (fun y => Real.exp (-q*y^2))
      (Real.exp (-q*x^2)*(-q*(2*x))) x := by
    intro x
    convert (((hasDerivAt_id x).pow 2).const_mul (-q)).exp using 1 <;>
      first | rfl | norm_num
  have hr := continuous_cumulative_cap hb (by simpa [uIcc_of_le hb] using hF)
    hw.continuousOn hFd (fun x hx => hd x)
    (by apply ContinuousOn.intervalIntegrable;simpa [uIcc_of_le hb] using hf)
    (hwp.intervalIntegrable 0 b) hcap
    (by intro x hx;apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le;nlinarith [hx.1])
    (Real.exp_pos _).le
  simpa [hF0] using hr

theorem gaussian_cumulative_full_cap
    {F f : ℝ → ℝ} {q b m c : ℝ} (hq : 0 < q) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hF : ContinuousOn F (Icc 0 b)) (hf : ContinuousOn f (Icc 0 b))
    (hFd : ∀ x ∈ Ioo 0 b, HasDerivAt F (f x) x) (hF0 : F 0 = 0)
    (hcap : ∀ x ∈ Icc 0 b, F x ≤ m*x+c) :
    (∫ x in (0:ℝ)..b, Real.exp (-q*x^2)*f x) ≤
      m*Real.sqrt (Real.pi/q)/2+c := by
  have hr := gaussian_cumulative_cap hq hb hF hf hFd hF0 hcap
  have hs := mul_le_mul_of_nonneg_left (gaussian_area_bound (b:=b) hq) hm
  linarith

#print axioms gaussian_cumulative_full_cap
end SynergyAnalytic
