import SynergyAnalytic.Peak
import SynergyAnalytic.CumulativeBoundary
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def weightLowD (x : ℝ) : ℝ :=
  Real.exp (baseLog (601/2500) x)*(-(601/2500:ℝ)*(2*x)+x⁻¹/3)
noncomputable def weightHighD (h x : ℝ) : ℝ := Real.exp (tailLog h x)*tailD h x

theorem weightLowD_integrable : IntervalIntegrable weightLowD volume peakX 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : x ∈ Icc peakX 1 := by simpa [uIcc_of_le peakX_le_one] using hx
  have xp : 0 < x := peakX_positive.trans_le hx'.1
  unfold weightLowD baseLog
  fun_prop (disch := exact xp.ne')

theorem weightHighD_integrable {h b : ℝ} (hh : 14 ≤ h) (hb : 1 ≤ b) :
    IntervalIntegrable (weightHighD h) volume 1 b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx' : x ∈ Icc 1 b := by simpa [uIcc_of_le hb] using hx
  have hx1 : 1 ≤ x := hx'.1
  have xp : 0 < x := by linarith
  have hp : 0 < h := by linarith
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hs : 0 < h+Real.log x := by linarith
  unfold weightHighD tailLog tailD
  fun_prop (disch := positivity)

theorem weightLowD_nonpos {x : ℝ} (hx : peakX ≤ x) : weightLowD x ≤ 0 := by
  have xp : 0 < x := peakX_positive.trans_le hx
  have hs : peakX^2 ≤ x^2 := by nlinarith [peakX_positive]
  have hm : 1 ≤ 6*(601/2500:ℝ)*x^2 := by nlinarith [peakX_equation]
  have hinv : x*x⁻¹ = 1 := mul_inv_cancel₀ xp.ne'
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have hn : x*(-(601/2500:ℝ)*(2*x)+x⁻¹/3) ≤ 0 := by nlinarith
  exact nonpos_of_mul_nonpos_right hn xp

theorem weightHighD_nonpos {h x : ℝ} (hh : 14 ≤ h) (hx : 1 ≤ x) :
    weightHighD h x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (tailD_nonpos hh hx)

theorem sourceShapeWeight_prefix_continuous (h : ℝ) :
    ContinuousOn (sourceShapeWeight h) (Icc 0 peakX) := by
  have hc : Continuous (fun x : ℝ => Real.exp (-(601/2500:ℝ)*x^2)*x^((1:ℝ)/3)) := by
    apply Continuous.mul
    · fun_prop
    · exact continuous_id.rpow_const (fun _ => Or.inr (by norm_num))
  apply hc.continuousOn.congr
  intro x hx
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx.1 (hx.2.trans peakX_le_one)
  simp [sourceShapeWeight,max_eq_right hl]

theorem sourceShapeWeight_nonneg {h x : ℝ} (hx : 0 ≤ x) : 0 ≤ sourceShapeWeight h x := by
  unfold sourceShapeWeight
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx _)) (sq_nonneg _)

/-- A finite full coupled moment estimate from precisely the original affine
cumulative mean-square cap.  The Gaussian/log moments have not been numerically
bounded in this theorem, and its hypotheses contain no desired-moment bound. -/
theorem shape_weight_cdf_bound
    {F f : ℝ → ℝ} {h b m c : ℝ}
    (hh : 14 ≤ h) (hb : 1 ≤ b)
    (hF : ContinuousOn F (Icc 0 b)) (hf : ContinuousOn f (Icc 0 b))
    (hFd : ∀ x ∈ Ioo 0 b, HasDerivAt F (f x) x) (hF0 : F 0 = 0)
    (hfp : ∀ x ∈ Icc 0 b, 0 ≤ f x)
    (hcap : ∀ x ∈ Icc 0 b, F x ≤ m*x+c) :
    (∫ x in (0:ℝ)..b, sourceShapeWeight h x*f x) ≤
      m*(universalPeak*peakX+∫ x in peakX..b, sourceShapeWeight h x)+c*universalPeak := by
  have ha : 0 ≤ peakX := peakX_positive.le
  have hab : peakX ≤ b := peakX_le_one.trans hb
  have hsub0 : Icc 0 peakX ⊆ Icc 0 b := Icc_subset_Icc le_rfl hab
  have hsubl : Icc peakX 1 ⊆ Icc 0 b := Icc_subset_Icc ha hb
  have hsubr : Icc 1 b ⊆ Icc 0 b := Icc_subset_Icc (by norm_num) le_rfl
  have hshl : ContinuousOn (sourceShapeWeight h) (uIcc peakX 1) :=
    sourceShapeWeight_continuousOn.mono (by
      rw [uIcc_of_le peakX_le_one]
      intro x hx;exact peakX_positive.trans_le hx.1)
  have hshr : ContinuousOn (sourceShapeWeight h) (uIcc 1 b) :=
    sourceShapeWeight_continuousOn.mono (by
      rw [uIcc_of_le hb]
      intro x hx;exact lt_of_lt_of_le (by norm_num) hx.1)
  have ht := two_piece_cumulative_cap peakX_le_one hb (sourceShapeWeight_peakX h)
    (by simpa [uIcc_of_le peakX_le_one] using hF.mono hsubl)
    (by simpa [uIcc_of_le hb] using hF.mono hsubr) hshl hshr
    (fun x hx => hFd x ⟨peakX_positive.trans hx.1,hx.2.trans_le hb⟩)
    (fun x hx => hFd x ⟨lt_trans (by norm_num) hx.1,hx.2⟩)
    (fun x hx => sourceShapeWeight_hasDerivAt_low (peakX_positive.trans hx.1) hx.2)
    (fun x hx => sourceShapeWeight_hasDerivAt_high hh hx.1)
    (by apply ContinuousOn.intervalIntegrable;simpa [uIcc_of_le peakX_le_one] using hf.mono hsubl)
    (by apply ContinuousOn.intervalIntegrable;simpa [uIcc_of_le hb] using hf.mono hsubr)
    weightLowD_integrable (weightHighD_integrable hh hb)
    (fun x hx => hcap x ⟨ha.trans hx.1,hx.2⟩)
    (fun x hx => weightLowD_nonpos hx.1)
    (fun x hx => weightHighD_nonpos hh hx.1)
    (sourceShapeWeight_nonneg (by linarith))
  have hfi0 : IntervalIntegrable f volume 0 peakX := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ha] using hf.mono hsub0
  have hFmass : (∫ x in (0:ℝ)..peakX, f x) = F peakX := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha (hF.mono hsub0)
      (fun x hx => hFd x ⟨hx.1,hx.2.trans_le hab⟩) hfi0,hF0,sub_zero]
  have hprefix : (∫ x in (0:ℝ)..peakX, sourceShapeWeight h x*f x) ≤ universalPeak*F peakX := by
    rw [← hFmass,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ha
      (hfi0.continuousOn_mul (by simpa [uIcc_of_le ha] using sourceShapeWeight_prefix_continuous h))
      (hfi0.const_mul universalPeak)
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (hfp x (hsub0 hx))
    rcases eq_or_lt_of_le hx.1 with he | hp
    · subst x
      simp [sourceShapeWeight,universalPeak]
      positivity
    · exact sourceShapeWeight_le_peak hh hp
  have htaili : IntervalIntegrable (fun x => sourceShapeWeight h x*f x) volume peakX b := by
    exact (hshl.intervalIntegrable.mul_continuousOn
      (by simpa [uIcc_of_le peakX_le_one] using hf.mono hsubl)).trans
      (hshr.intervalIntegrable.mul_continuousOn
        (by simpa [uIcc_of_le hb] using hf.mono hsubr))
  have hprefixi : IntervalIntegrable (fun x => sourceShapeWeight h x*f x) volume 0 peakX :=
    hfi0.continuousOn_mul (by simpa [uIcc_of_le ha] using sourceShapeWeight_prefix_continuous h)
  rw [← intervalIntegral.integral_add_adjacent_intervals hprefixi htaili]
  linarith

#print axioms shape_weight_cdf_bound
end SynergyAnalytic
