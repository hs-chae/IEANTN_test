import SynergyAnalytic.ActualBasis
import SynergyAnalytic.GaussianCDF
import SynergyAnalytic.WeightedError
import SynergyAnalytic.ZetaPointwise
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerBetaA.ActualObject
set_option maxHeartbeats 0

noncomputable def gaussian0 (x : ℝ) : ℝ := Real.exp (-(601/2500:ℝ)*x^2)
noncomputable def gaussianArea : ℝ := Real.sqrt (Real.pi/(601/2500:ℝ))/2

theorem shape_weight_identity {h x : ℝ} (hx : 0 ≤ x) :
    gaussian0 x*zetaShape h x^2 = sourceShapeWeight h x := by
  have he : (x^((1:ℝ)/6))^2 = x^((1:ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hx (1/6) 2]
    norm_num
  unfold gaussian0 zetaShape sourceShapeWeight
  rw [mul_pow,he]
  ring

theorem sourceShapeWeight_intervalIntegrable {h b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (sourceShapeWeight h) volume 0 b := by
  have ha := peakX_positive.le
  have h0 : IntervalIntegrable (sourceShapeWeight h) volume 0 peakX :=
    ContinuousOn.intervalIntegrable (by simpa [uIcc_of_le ha] using sourceShapeWeight_prefix_continuous h)
  have h1 : IntervalIntegrable (sourceShapeWeight h) volume peakX b := by
    apply ContinuousOn.intervalIntegrable
    exact sourceShapeWeight_continuousOn.mono (by
      rw [uIcc_of_le (peakX_le_one.trans hb)]
      intro x hx;exact peakX_positive.trans_le hx.1)
  exact h0.trans h1

theorem actual_mollifier_gaussian_bound
    {T b m1 m2 : ℝ} (hT : 1 < T) (hb : 0 ≤ b) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hmean : ∀ t > 0,
      (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
        (m1*t+m2*T)*Real.log T) :
    (∫ x in (0:ℝ)..b, gaussian0 x*mollifierMassD T x) ≤
      (T*Real.log T)*(m1*gaussianArea+m2) := by
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : ∀ x ∈ Icc 0 b, mollifierMass T x ≤
      (T*Real.log T*m1)*x+(T*Real.log T*m2) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he | hp
    · subst x
      simp only [mollifierMass,zero_mul,intervalIntegral.integral_same,add_zero,zero_add]
      positivity
    · have hh := hmean (x*T) (mul_pos hp hTp)
      convert hh using 1 <;> first | rfl | ring
  have hr := gaussian_cumulative_full_cap (by norm_num : (0:ℝ)<601/2500) hb
    (show 0 ≤ T*Real.log T*m1 by positivity) (mollifierMass_continuous T).continuousOn
    (mollifierMassD_continuous T).continuousOn
    (fun x hx => mollifierMass_hasDerivAt T x) (by simp [mollifierMass]) hc
  convert hr using 1 <;> first | rfl | (simp only [gaussian0,gaussianArea];ring)

/-- A continuous Gaussian bound for the ACTUAL mollified error from the two
original zeta bounds and the original mollifier mean square.  All height
dependence factors through three universal basis integrals. -/
theorem actual_finite_error_three_basis
    {T h r eps eta b m1 m2 : ℝ}
    (hT : 1 < T) (hh : 14 ≤ h) (hhT : h ≤ Real.log T) (hb : 1 ≤ b)
    (hr : (1461/1000:ℝ)/zetaScale T ≤ r) (he : 0 < eps) (ht : 0 < eta)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hLow : ∀ u : ℝ, 0 ≤ u → u ≤ 3 → ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ))
    (hHigh : ∀ u : ℝ, 3 ≤ u → ‖riemannZeta (vertical (1/2) u)‖ ≤
      (611/1000:ℝ)*u^((1:ℝ)/6)*Real.log u)
    (hmean : ∀ t > 0,
      (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
        (m1*t+m2*T)*Real.log T) :
    (∫ x in (0:ℝ)..b, T*gaussian0 x*‖mollifiedError T (vertical (1/2) (x*T))‖^2) ≤
      (1+eps)*(zetaScale T)^2*(T*Real.log T)*
        ((1+eta)*(m1*(basisZero b+(2/h)*basisOne b+(1/h^2)*basisTwo b)+m2*universalPeak)+
          (1+1/eta)*r^2*(m1*gaussianArea+m2))+(1+1/eps)*T*gaussianArea := by
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hamp : 0 < zetaScale T := by unfold zetaScale;positivity
  have hrp : 0 ≤ r := (div_nonneg (by norm_num) hamp.le).trans hr
  let z : ℝ → ℂ := fun x => riemannZeta (vertical (1/2) (x*T))
  let v : ℝ → ℂ := fun x => mollifier T (vertical (1/2) (x*T))
  have hz0 : Continuous (fun u : ℝ => riemannZeta (vertical (1/2) u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hn : vertical (1/2) u ≠ (1:ℂ) := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [vertical] at hre
    exact (differentiableAt_riemannZeta hn).continuousAt.comp
      ((vertical_continuous (1/2)).continuousAt)
  have hz : Continuous z := hz0.comp (continuous_id.mul_const T)
  have hv : Continuous v := (mollifier_continuous T).comp
    ((vertical_continuous (1/2)).comp (continuous_id.mul_const T))
  have hwi : IntervalIntegrable gaussian0 volume 0 b :=
    (by unfold gaussian0;fun_prop : Continuous gaussian0).intervalIntegrable 0 b
  have hfi : IntervalIntegrable (fun x => gaussian0 x*mollifierMassD T x) volume 0 b :=
    hwi.mul_continuousOn (mollifierMassD_continuous T).continuousOn
  have hsi : IntervalIntegrable (fun x => gaussian0 x*zetaShape h x^2*mollifierMassD T x) volume 0 b := by
    apply ((sourceShapeWeight_intervalIntegrable (h:=h) hb).mul_continuousOn
      (mollifierMassD_continuous T).continuousOn).congr_uIoo
    intro x hx
    have hx' : x ∈ Ioo 0 b := by simpa [uIoo_of_le (by linarith : (0:ℝ)≤b)] using hx
    change sourceShapeWeight h x*mollifierMassD T x = gaussian0 x*zetaShape h x^2*mollifierMassD T x
    rw [shape_weight_identity hx'.1.le]
  have hc := actual_mollifier_three_basis hTp hh hb hmean
  have hc' : (∫ x in (0:ℝ)..b, gaussian0 x*zetaShape h x^2*mollifierMassD T x) ≤
      (T*Real.log T)*(m1*(basisZero b+(2/h)*basisOne b+(1/h^2)*basisTwo b)+m2*universalPeak) := by
    have heq : (∫ x in (0:ℝ)..b, gaussian0 x*zetaShape h x^2*mollifierMassD T x) =
        ∫ x in (0:ℝ)..b, sourceShapeWeight h x*mollifierMassD T x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc 0 b := by simpa [uIcc_of_le (by linarith : (0:ℝ)≤b)] using hx
      change gaussian0 x*zetaShape h x^2*mollifierMassD T x = sourceShapeWeight h x*mollifierMassD T x
      rw [shape_weight_identity hx'.1]
    rw [heq]
    exact hc
  have hg := actual_mollifier_gaussian_bound hT (by linarith : (0:ℝ)≤b) hm1 hm2 hmean
  have harea : (∫ x in (0:ℝ)..b, gaussian0 x) ≤ gaussianArea :=
    gaussian_area_bound (by norm_num : (0:ℝ)<601/2500)
  have hfinal := weighted_error_of_two_moments hTp.le hamp.le hrp he ht (by linarith : (0:ℝ)≤b)
    hz hv hwi hfi hsi (by intro x hx;unfold gaussian0;positivity)
    (by intro x hx;exact zetaShape_nonneg (by linarith) hx.1.le)
    (by intro x;rfl)
    (by intro x hx;exact zeta_pointwise_source hT (by linarith) hhT hx.1 hr hLow hHigh)
    hc' hg harea
  convert hfinal using 1 <;> first | rfl | ring

#print axioms actual_finite_error_three_basis
end SynergyAnalytic
