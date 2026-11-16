import SynergyAnalytic.Peak
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def baseWeight (x : ℝ) : ℝ :=
  Real.exp (-(601/2500:ℝ)*x^2)*x^((1:ℝ)/3)
noncomputable def basisZero (b : ℝ) : ℝ := universalPeak*peakX+∫ x in peakX..b, baseWeight x
noncomputable def basisOne (b : ℝ) : ℝ := ∫ x in (1:ℝ)..b, baseWeight x*Real.log x
noncomputable def basisTwo (b : ℝ) : ℝ := ∫ x in (1:ℝ)..b, baseWeight x*(Real.log x)^2

theorem baseWeight_continuous : Continuous baseWeight := by
  unfold baseWeight
  apply Continuous.mul
  · fun_prop
  · exact continuous_id.rpow_const (fun _ => Or.inr (by norm_num))

theorem sourceShapeWeight_low_eq {h x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    sourceShapeWeight h x = baseWeight x := by
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx hx1
  simp [sourceShapeWeight,baseWeight,max_eq_right hl]

theorem sourceShapeWeight_high_expand {h x : ℝ} (hh : h ≠ 0) (hx : 1 ≤ x) :
    sourceShapeWeight h x = baseWeight x + (2/h)*(baseWeight x*Real.log x)+
      (1/h^2)*(baseWeight x*(Real.log x)^2) := by
  unfold sourceShapeWeight baseWeight
  rw [max_eq_left (Real.log_nonneg hx)]
  field_simp
  <;> ring

/-- Exactly three universal basis integrals determine every height-dependent
moment.  There is no interpolation of computed height profiles in this identity. -/
theorem universal_three_basis {h b : ℝ} (hh : h ≠ 0) (hb : 1 ≤ b) :
    universalPeak*peakX + (∫ x in peakX..b, sourceShapeWeight h x) =
      basisZero b + (2/h)*basisOne b + (1/h^2)*basisTwo b := by
  have hbi : IntervalIntegrable baseWeight volume 1 b := baseWeight_continuous.intervalIntegrable _ _
  have hli : IntervalIntegrable (fun x => baseWeight x*Real.log x) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Icc 1 b := by simpa [uIcc_of_le hb] using hx
    exact baseWeight_continuous.continuousAt.continuousWithinAt.mul
      ((Real.continuousAt_log (by linarith [hx'.1] : x≠0)).continuousWithinAt)
  have hl2i : IntervalIntegrable (fun x => baseWeight x*(Real.log x)^2) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Icc 1 b := by simpa [uIcc_of_le hb] using hx
    exact baseWeight_continuous.continuousAt.continuousWithinAt.mul
      (((Real.continuousAt_log (by linarith [hx'.1] : x≠0)).continuousWithinAt).pow 2)
  have hwlo : (∫ x in peakX..1, sourceShapeWeight h x) = ∫ x in peakX..1, baseWeight x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc peakX 1 := by simpa [uIcc_of_le peakX_le_one] using hx
    exact sourceShapeWeight_low_eq (peakX_positive.le.trans hx'.1) hx'.2
  have hwhi : (∫ x in (1:ℝ)..b, sourceShapeWeight h x) =
      (∫ x in (1:ℝ)..b, baseWeight x) + (2/h)*basisOne b+(1/h^2)*basisTwo b := by
    calc
      _ = ∫ x in (1:ℝ)..b, baseWeight x+(2/h)*(baseWeight x*Real.log x)+
          (1/h^2)*(baseWeight x*(Real.log x)^2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc 1 b := by simpa [uIcc_of_le hb] using hx
        exact sourceShapeWeight_high_expand hh hx'.1
      _ = _ := by
        rw [intervalIntegral.integral_add (hbi.add (hli.const_mul _)) (hl2i.const_mul _),
          intervalIntegral.integral_add hbi (hli.const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
        rfl
  have hwli : IntervalIntegrable (sourceShapeWeight h) volume peakX 1 := by
    apply ContinuousOn.intervalIntegrable
    exact sourceShapeWeight_continuousOn.mono (by
      rw [uIcc_of_le peakX_le_one]
      intro x hx;exact peakX_positive.trans_le hx.1)
  have hwri : IntervalIntegrable (sourceShapeWeight h) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    exact sourceShapeWeight_continuousOn.mono (by
      rw [uIcc_of_le hb]
      intro x hx;exact lt_of_lt_of_le (by norm_num) hx.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hwli hwri,hwlo,hwhi]
  unfold basisZero
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (baseWeight_continuous.intervalIntegrable peakX 1) hbi]
  ring

#print axioms universal_three_basis
end SynergyAnalytic
