import Mathlib

namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- A continuous Abel bound from a cumulative affine cap.  The cap may have a
nonzero intercept; no pointwise bound on its derivative is assumed. -/
theorem continuous_cumulative_cap
    {F f w wp : ℝ → ℝ} {a b m c : ℝ}
    (hab : a ≤ b)
    (hF : ContinuousOn F (uIcc a b))
    (hw : ContinuousOn w (uIcc a b))
    (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hwd : ∀ x ∈ Ioo a b, HasDerivAt w (wp x) x)
    (hf : IntervalIntegrable f volume a b)
    (hwp : IntervalIntegrable wp volume a b)
    (hcap : ∀ x ∈ Icc a b, F x ≤ m*x+c)
    (hdec : ∀ x ∈ Icc a b, wp x ≤ 0)
    (hwb : 0 ≤ w b) :
    w a*F a + (∫ x in a..b, w x*f x) ≤
      m*(w a*a + ∫ x in a..b, w x) + c*w a := by
  let G : ℝ → ℝ := fun x => m*x+c-F x
  have hG : ContinuousOn G (uIcc a b) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn.sub hF
  have hGd : ∀ x ∈ Ioo a b, HasDerivAt G (m-f x) x := by
    intro x hx
    change HasDerivAt (fun y => m*y+c-F y) (m-f x) x
    convert ((((hasDerivAt_id x).const_mul m).add_const c).sub (hFd x hx)) using 1 <;>
      first | rfl | (funext y; rfl) | simp only [id_eq,mul_one]
  have hint : IntervalIntegrable (fun x => m-f x) volume a b :=
    intervalIntegrable_const.sub hf
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hw hG (fun x hx => hwd x (by simpa [min_eq_left hab,max_eq_right hab] using hx))
    (fun x hx => hGd x (by simpa [min_eq_left hab,max_eq_right hab] using hx)) hwp hint
  have hsign : (∫ x in a..b, wp x*G x) ≤ 0 := by
    have hn : 0 ≤ (∫ x in a..b, -(wp x*G x)) := by
      apply intervalIntegral.integral_nonneg hab
      intro x hx
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hdec x hx)
        (sub_nonneg.mpr (hcap x hx)))
    simpa only [intervalIntegral.integral_neg,neg_nonneg] using hn
  have hbound : 0 ≤ w b*G b :=
    mul_nonneg hwb (sub_nonneg.mpr (hcap b ⟨hab,le_rfl⟩))
  have hwi : IntervalIntegrable w volume a b := hw.intervalIntegrable
  have hwfi : IntervalIntegrable (fun x => w x*f x) volume a b := hf.continuousOn_mul hw
  have hexpand : (∫ x in a..b, w x*(m-f x)) =
      m*(∫ x in a..b, w x) - ∫ x in a..b, w x*f x := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hwi.mul_const m) hwfi,
      intervalIntegral.integral_mul_const]
    ring
  rw [hexpand] at hip
  dsimp [G] at hip hbound
  nlinarith

/-- If a decreasing weight has a flat prefix, the affine cumulative bound costs
exactly its area times the slope plus its maximum times the intercept. -/
theorem flat_prefix_cumulative_cap
    {F f w wp : ℝ → ℝ} {a b m c M : ℝ}
    (hab : a ≤ b) (hflat : w a = M)
    (hF : ContinuousOn F (uIcc a b))
    (hw : ContinuousOn w (uIcc a b))
    (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hwd : ∀ x ∈ Ioo a b, HasDerivAt w (wp x) x)
    (hf : IntervalIntegrable f volume a b)
    (hwp : IntervalIntegrable wp volume a b)
    (hcap : ∀ x ∈ Icc a b, F x ≤ m*x+c)
    (hdec : ∀ x ∈ Icc a b, wp x ≤ 0)
    (hwb : 0 ≤ w b) :
    M*F a + (∫ x in a..b, w x*f x) ≤
      m*(M*a + ∫ x in a..b, w x) + c*M := by
  simpa [hflat] using continuous_cumulative_cap hab hF hw hFd hwd hf hwp hcap hdec hwb

#print axioms continuous_cumulative_cap
#print axioms flat_prefix_cumulative_cap
end SynergyAnalytic
