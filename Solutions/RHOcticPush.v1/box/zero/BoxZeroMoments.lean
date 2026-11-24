import BoxZeroKernel
import BoxIntegrability

/-! Exact signed-moment transport for the full Box kernel. The singular baseline
is integrated analytically; the entire small interval is retained and bounded. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
set_option maxHeartbeats 0

noncomputable def regular (y : ℝ) : ℝ :=
  (|F y| - if y ≤ 1 then 1 else 0) / y
noncomputable def regularWeight (q y : ℝ) : ℝ := regular y * log (y/q)
noncomputable def singularWeight (q y : ℝ) : ℝ :=
  (Iic (1:ℝ)).indicator (fun y : ℝ => log (y/q)/y) y

lemma regular_zero (y : ℝ) : regular y = BoxMellinInputs.v1.integrand 0 y := by
  simp [regular,BoxMellinInputs.v1.integrand,F]

lemma regular_one (y : ℝ) : regular y * log y = BoxMellinInputs.v1.integrand 1 y := by
  simp only [regular,BoxMellinInputs.v1.integrand,F,pow_one]
  ring

lemma regular_integrable : IntegrableOn regular (Ioi (0:ℝ)) := by
  have he : regular = BoxMellinInputs.v1.integrand 0 := funext regular_zero
  rw [he]
  exact RHOcticPush.Box.actual_integrable (j := 0) (by norm_num)

lemma regular_log_integrable : IntegrableOn (fun y => regular y * log y) (Ioi (0:ℝ)) := by
  simpa only [regular_one] using RHOcticPush.Box.actual_integrable (j := 1) (by norm_num)

lemma regularWeight_integrable {q : ℝ} (hq : 0<q) :
    IntegrableOn (regularWeight q) (Ioi (0:ℝ)) := by
  have hi := regular_log_integrable.sub (regular_integrable.mul_const (log q))
  apply hi.congr_fun _ measurableSet_Ioi
  intro y hy
  dsimp [regularWeight]
  rw [Real.log_div (ne_of_gt hy) hq.ne']
  ring

lemma regularWeight_integral {q : ℝ} (hq : 0<q) :
    (∫ y in Ioi (0:ℝ),regularWeight q y) =
      IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 -
        log q * IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 := by
  have he : (∫ y in Ioi (0:ℝ),regularWeight q y) =
      (∫ y in Ioi (0:ℝ),regular y * log y) -
        log q * (∫ y in Ioi (0:ℝ),regular y) := by
    calc
      _ = ∫ y in Ioi (0:ℝ),regular y * log y - log q * regular y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        dsimp [regularWeight]
        rw [Real.log_div (ne_of_gt hy) hq.ne']
        ring
      _ = _ := by rw [integral_sub regular_log_integrable (regular_integrable.const_mul _),
        integral_const_mul]
  rw [he]
  change (∫ y in Ioi (0:ℝ),regular y * log y) - log q*(∫ y in Ioi (0:ℝ),regular y) =
    (∫ y in Ioi (0:ℝ),BoxMellinInputs.v1.integrand 1 y) -
      log q*(∫ y in Ioi (0:ℝ),BoxMellinInputs.v1.integrand 0 y)
  have he1 : (fun y : ℝ => regular y * log y) = BoxMellinInputs.v1.integrand 1 :=
    funext regular_one
  have he0 : regular = BoxMellinInputs.v1.integrand 0 := funext regular_zero
  rw [he1,he0]

lemma singularWeight_integrable {c q : ℝ} (hc : 0<c) (hc1 : c≤1) (hq : 0<q) :
    IntegrableOn (singularWeight q) (Ioi c) := by
  rw [show singularWeight q = (Iic (1:ℝ)).indicator (fun y : ℝ => log (y/q)/y) by rfl,
    integrableOn_indicator_iff measurableSet_Iic]
  have he : Iic (1:ℝ) ∩ Ioi c = Ioc c 1 := by ext y;simp [and_comm]
  rw [he]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hc1).mp
  apply ContinuousOn.intervalIntegrable
  intro y hy
  rw [uIcc_of_le hc1] at hy
  have hy0 : y ≠ 0 := (hc.trans_le hy.1).ne'
  exact (((continuousAt_id.div_const q).log (div_ne_zero hy0 hq.ne')).div
    continuousAt_id hy0).continuousWithinAt

lemma singularWeight_integral {c q : ℝ} (hc : 0<c) (hc1 : c≤1) (hq : 0<q) :
    (∫ y in Ioi c,singularWeight q y) =
      ((log (1/q))^2-(log (c/q))^2)/2 := by
  change (∫ y in Ioi c,(Iic (1:ℝ)).indicator (fun y : ℝ => log (y/q)/y) y) = _
  rw [setIntegral_indicator measurableSet_Iic]
  have he : Ioi c ∩ Iic (1:ℝ) = Ioc c 1 := by ext y;rfl
  rw [he,← intervalIntegral.integral_of_le hc1]
  have hd (y : ℝ) (hy : y ∈ uIcc c 1) :
      HasDerivAt (fun y : ℝ => (log y-log q)^2/2) (log (y/q)/y) y := by
    rw [uIcc_of_le hc1] at hy
    have hy0 : y ≠ 0 := (hc.trans_le hy.1).ne'
    apply (((Real.hasDerivAt_log hy0).sub_const (log q)).pow 2 |>.div_const 2).congr_deriv
    rw [Real.log_div hy0 hq.ne']
    ring
  have hi : IntervalIntegrable (fun y : ℝ => log (y/q)/y) volume c 1 := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le hc1] at hy
    have hy0 : y ≠ 0 := (hc.trans_le hy.1).ne'
    exact (((continuousAt_id.div_const q).log (div_ne_zero hy0 hq.ne')).div
      continuousAt_id hy0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  rw [Real.log_div (by norm_num : (1:ℝ)≠0) hq.ne',Real.log_one,
    Real.log_div hc.ne' hq.ne']
  ring

lemma actualWeight_split {q y : ℝ} (hq : 0<q) (hy : 0<y) :
    |F y|/y*log (y/q) = regularWeight q y + singularWeight q y := by
  unfold regularWeight regular singularWeight
  by_cases hy1 : y≤1
  · rw [if_pos hy1,Set.indicator_of_mem (show y ∈ Iic (1:ℝ) from hy1)]
    ring
  · rw [if_neg hy1,Set.indicator_of_notMem (show y ∉ Iic (1:ℝ) from hy1)]
    ring

lemma actualWeight_integrable {c q : ℝ} (hc : 0<c) (hc1 : c≤1) (hq : 0<q) :
    IntegrableOn (fun y : ℝ => |F y|/y*log (y/q)) (Ioi c) := by
  have hi := ((regularWeight_integrable hq).mono_set (Ioi_subset_Ioi hc.le)).add
    (singularWeight_integrable hc hc1 hq)
  apply hi.congr_fun _ measurableSet_Ioi
  intro y hy
  exact (actualWeight_split hq (hc.trans hy)).symm

lemma regularWeight_low_lower {c q : ℝ} (hc : 0<c) (hc1 : c≤1) (hq : 0<q)
    (hlog : log (c/q) ≤ 1) :
    -(c^2/12) ≤ ∫ y in Ioc (0:ℝ) c,regularWeight q y := by
  have hi : IntegrableOn (regularWeight q) (Ioc (0:ℝ) c) :=
    (regularWeight_integrable hq).mono_set Ioc_subset_Ioi_self
  have hleft : IntegrableOn (fun y : ℝ => -y/6) (Ioc (0:ℝ) c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp
      ((by fun_prop : Continuous (fun y : ℝ => -y/6)).intervalIntegrable _ _)
  have hh : (∫ y in Ioc (0:ℝ) c,-y/6) ≤
      ∫ y in Ioc (0:ℝ) c,regularWeight q y := by
    apply integral_mono_ae hleft hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy1 : y≤1 := hy.2.trans hc1
    have hr : regular y ≤ 0 := by
      unfold regular
      rw [if_pos hy1]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (F_abs y)) hy.1.le
    have hlo : -y/6 ≤ regular y := by
      have hd := RHOcticPush.Box.sinc_defect hy.1
      rw [← F_eq hy.1.ne'] at hd
      unfold regular
      rw [if_pos hy1]
      apply (le_div_iff₀ hy.1).mpr
      nlinarith [(abs_le.mp hd).1]
    have hlog1 : log (y/q)≤1 :=
      (Real.log_le_log (div_pos hy.1 hq)
        (div_le_div_of_nonneg_right hy.2 hq.le)).trans hlog
    unfold regularWeight
    by_cases hl : 0≤log (y/q)
    · have hh := mul_le_mul_of_nonneg_right hlo hl
      have he : (-y/6)*log (y/q) ≥ -y/6 := by
        nlinarith [mul_nonneg hy.1.le (sub_nonneg.mpr hlog1)]
      exact he.trans hh
    · exact (by linarith : -y/6≤0).trans (mul_nonneg_of_nonpos_of_nonpos hr (le_of_not_ge hl))
  rw [← intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_div,
    intervalIntegral.integral_neg,integral_id] at hh
  norm_num at hh
  linarith

/-- Exact full regularization, including the singular baseline and low interval. -/
theorem actualWeight_integral {c q : ℝ} (hc : 0<c) (hc1 : c≤1) (hq : 0<q) :
    (∫ y in Ioi c,|F y|/y*log (y/q)) =
      IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 -
        log q*IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 +
        ((log (1/q))^2-(log (c/q))^2)/2 -
          ∫ y in Ioc (0:ℝ) c,regularWeight q y := by
  have hi := regularWeight_integrable hq
  have hsplit : (∫ y in Ioi (0:ℝ),regularWeight q y) =
      (∫ y in Ioc (0:ℝ) c,regularWeight q y) + ∫ y in Ioi c,regularWeight q y := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hc.le))
  have he : (∫ y in Ioi c,|F y|/y*log (y/q)) =
      (∫ y in Ioi c,regularWeight q y) + ∫ y in Ioi c,singularWeight q y := by
    calc
      _ = ∫ y in Ioi c,regularWeight q y + singularWeight q y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        exact actualWeight_split hq (hc.trans hy)
      _ = _ := integral_add (hi.mono_set (Ioi_subset_Ioi hc.le))
        (singularWeight_integrable hc hc1 hq)
  rw [regularWeight_integral hq] at hsplit
  rw [he,singularWeight_integral hc hc1 hq]
  linarith

#print axioms actualWeight_integral
#print axioms regularWeight_low_lower
end RHOcticPush.BoxZero
