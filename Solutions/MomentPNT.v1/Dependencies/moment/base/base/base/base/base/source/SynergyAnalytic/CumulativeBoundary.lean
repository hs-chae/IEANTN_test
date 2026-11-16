import SynergyAnalytic.Cumulative
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- The boundary-preserving form telescopes across corners of a majorant. -/
theorem cumulative_cap_boundary
    {F f w wp : ℝ → ℝ} {a b m c : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (uIcc a b)) (hw : ContinuousOn w (uIcc a b))
    (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hwd : ∀ x ∈ Ioo a b, HasDerivAt w (wp x) x)
    (hf : IntervalIntegrable f volume a b) (hwp : IntervalIntegrable wp volume a b)
    (hcap : ∀ x ∈ Icc a b, F x ≤ m*x+c)
    (hdec : ∀ x ∈ Icc a b, wp x ≤ 0) :
    w a*F a + (∫ x in a..b, w x*f x) ≤ w b*F b +
      m*(w a*a-w b*b+∫ x in a..b, w x) + c*(w a-w b) := by
  let G : ℝ → ℝ := fun x => m*x+c-F x
  have hG : ContinuousOn G (uIcc a b) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn.sub hF
  have hGd : ∀ x ∈ Ioo a b, HasDerivAt G (m-f x) x := by
    intro x hx
    change HasDerivAt (fun y => m*y+c-F y) (m-f x) x
    convert ((((hasDerivAt_id x).const_mul m).add_const c).sub (hFd x hx)) using 1 <;>
      first | rfl | simp only [mul_one]
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hw hG (fun x hx => hwd x (by simpa [min_eq_left hab,max_eq_right hab] using hx))
    (fun x hx => hGd x (by simpa [min_eq_left hab,max_eq_right hab] using hx)) hwp
    (intervalIntegrable_const.sub hf)
  have hsign : (∫ x in a..b, wp x*G x) ≤ 0 := by
    have hn : 0 ≤ (∫ x in a..b, -(wp x*G x)) := by
      apply intervalIntegral.integral_nonneg hab
      intro x hx
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hdec x hx)
        (sub_nonneg.mpr (hcap x hx)))
    simpa only [intervalIntegral.integral_neg,neg_nonneg] using hn
  have hwi : IntervalIntegrable w volume a b := hw.intervalIntegrable
  have hwfi : IntervalIntegrable (fun x => w x*f x) volume a b := hf.continuousOn_mul hw
  have hexpand : (∫ x in a..b, w x*(m-f x)) =
      m*(∫ x in a..b, w x) - ∫ x in a..b, w x*f x := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hwi.mul_const m) hwfi,
      intervalIntegral.integral_mul_const]
    ring
  rw [hexpand] at hip
  dsimp [G] at hip
  nlinarith

/-- A corner in the weight requires no differentiability assumption at the
corner itself.  This covers log-positive weights and two-tangent Gaussian bounds. -/
theorem two_piece_cumulative_cap
    {F f w wp wq : ℝ → ℝ} {a s b m c M : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) (hflat : w a = M)
    (hFl : ContinuousOn F (uIcc a s)) (hFr : ContinuousOn F (uIcc s b))
    (hwl : ContinuousOn w (uIcc a s)) (hwr : ContinuousOn w (uIcc s b))
    (hFdl : ∀ x ∈ Ioo a s, HasDerivAt F (f x) x)
    (hFdr : ∀ x ∈ Ioo s b, HasDerivAt F (f x) x)
    (hwdl : ∀ x ∈ Ioo a s, HasDerivAt w (wp x) x)
    (hwdr : ∀ x ∈ Ioo s b, HasDerivAt w (wq x) x)
    (hfl : IntervalIntegrable f volume a s) (hfr : IntervalIntegrable f volume s b)
    (hwpi : IntervalIntegrable wp volume a s) (hwqi : IntervalIntegrable wq volume s b)
    (hcap : ∀ x ∈ Icc a b, F x ≤ m*x+c)
    (hdecl : ∀ x ∈ Icc a s, wp x ≤ 0) (hdecr : ∀ x ∈ Icc s b, wq x ≤ 0)
    (hwb : 0 ≤ w b) :
    M*F a + (∫ x in a..b, w x*f x) ≤
      m*(M*a+∫ x in a..b, w x) + c*M := by
  have hl := cumulative_cap_boundary has hFl hwl hFdl hwdl hfl hwpi
    (fun x hx => hcap x ⟨hx.1,hx.2.trans hsb⟩) hdecl
  have hr := cumulative_cap_boundary hsb hFr hwr hFdr hwdr hfr hwqi
    (fun x hx => hcap x ⟨has.trans hx.1,hx.2⟩) hdecr
  have hbound : w b*F b ≤ w b*(m*b+c) :=
    mul_le_mul_of_nonneg_left (hcap b ⟨has.trans hsb,le_rfl⟩) hwb
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfl.continuousOn_mul hwl) (hfr.continuousOn_mul hwr),
    ← intervalIntegral.integral_add_adjacent_intervals hwl.intervalIntegrable hwr.intervalIntegrable]
  rw [hflat] at hl
  nlinarith

#print axioms cumulative_cap_boundary
#print axioms two_piece_cumulative_cap
end SynergyAnalytic
