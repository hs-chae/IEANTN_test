import BoxIntegrability

namespace RHOcticPush.BoxMellin
open Real MeasureTheory Set Filter RHOcticPush.Box
open scoped Topology
set_option maxHeartbeats 0

noncomputable def packet (s y : ℝ) : ℝ := raw 0 y * Real.exp (s * Real.log y)
noncomputable def packetDeriv (s y : ℝ) : ℝ := packet s y * Real.log y
noncomputable def regularizedMellin (s : ℝ) : ℝ := ∫ y in Ioi (0:ℝ), packet s y
noncomputable def majorant (y : ℝ) : ℝ := if y ≤ 1 then 1 else 4 * y ^ (-3/2:ℝ)

lemma packet_measurable (s : ℝ) : Measurable (packet s) := by
  exact (raw_measurable 0).mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul Real.measurable_log))

lemma packetDeriv_measurable (s : ℝ) : Measurable (packetDeriv s) :=
  (packet_measurable s).mul Real.measurable_log

lemma packet_derivative (s y : ℝ) :
    HasDerivAt (fun t => packet t y) (packetDeriv s y) s := by
  have h := (((hasDerivAt_id s).mul_const (Real.log y)).exp).const_mul (raw 0 y)
  simpa [packet,packetDeriv,mul_assoc] using h

lemma raw_small_sharp {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖raw 0 y‖ ≤ y/6 := by
  have h := div_le_div_of_nonneg_right (sinc_defect hy) hy.le
  have he : y^2/6/y=y/6 := by field_simp
  rw [he] at h
  simpa [raw, if_pos hy1, Real.norm_eq_abs, abs_div,abs_of_pos hy] using h

lemma raw_large_sharp {y : ℝ} (hy : 1 < y) : ‖raw 0 y‖ ≤ 1/y^2 := by
  have hy0 : 0<y := by linarith
  have h := div_le_div_of_nonneg_right
    (show |Real.sin y/y| ≤ 1/y from by
      rw [abs_div,abs_of_pos hy0]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) hy0.le) hy0.le
  simpa [raw, if_neg hy.not_ge, Real.norm_eq_abs,abs_div,abs_of_pos hy0,div_div,
    pow_two,div_eq_mul_inv] using h

lemma log_small {y : ℝ} (hy : 0<y) (hy1 : y≤1) :
    |Real.log y| ≤ 2*y^(-1/2:ℝ) := by
  have h := Real.log_le_rpow_div (inv_nonneg.mpr hy.le)
    (show (0:ℝ)<1/2 by norm_num)
  rw [Real.log_inv, Real.inv_rpow hy.le] at h
  rw [abs_of_nonpos (Real.log_nonpos hy.le hy1),
    show (-1/2:ℝ)=-(1/2:ℝ) by ring, Real.rpow_neg hy.le]
  linarith

lemma derivative_small {s y : ℝ} (hs : (-1/4:ℝ)≤ s) (hy : 0<y) (hy1 : y≤1) :
    ‖packetDeriv s y‖ ≤ 1 := by
  have hr := Real.rpow_le_rpow_of_exponent_ge hy hy1 hs
  have hlog := log_small hy hy1
  have hraw := raw_small_sharp hy hy1
  have he : Real.exp (s*Real.log y)=y^s := by rw [Real.rpow_def_of_pos hy]; congr 1;ring
  have hn : ‖packetDeriv s y‖ = ‖raw 0 y‖ * y^s * |Real.log y| := by
    simp [packetDeriv,packet, norm_mul,he,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hy.le s)]
  rw [hn]
  calc
    _ ≤ (y/6)*y^((-1/4:ℝ))*(2*y^(-1/2:ℝ)) := by gcongr
    _ = (1/3:ℝ)*y^(1/4:ℝ) := by
      calc
        _ = (1/3:ℝ)*((y^(1:ℝ)*y^((-1/4:ℝ)))*y^(-1/2:ℝ)) := by
          rw [Real.rpow_one];ring
        _ = _ := by rw [← Real.rpow_add hy,← Real.rpow_add hy];norm_num
    _ ≤ 1 := by
      have h := Real.rpow_le_one hy.le hy1 (show (0:ℝ)≤1/4 by norm_num)
      linarith

lemma derivative_large {s y : ℝ} (hs : s≤(1/4:ℝ)) (hy : 1<y) :
    ‖packetDeriv s y‖ ≤ 4*y^(-3/2:ℝ) := by
  have hy0 : 0<y := by linarith
  have hr := Real.rpow_le_rpow_of_exponent_le hy.le hs
  have hlog : |Real.log y| ≤ 4*y^(1/4:ℝ) := by
    rw [abs_of_nonneg (Real.log_nonneg hy.le)]
    have h := Real.log_le_rpow_div hy0.le (show (0:ℝ)<1/4 by norm_num)
    linarith
  have hraw := raw_large_sharp hy
  have he : Real.exp (s*Real.log y)=y^s := by rw [Real.rpow_def_of_pos hy0];congr 1;ring
  have hn : ‖packetDeriv s y‖ = ‖raw 0 y‖ * y^s * |Real.log y| := by
    simp [packetDeriv,packet,norm_mul,he,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hy0.le s)]
  rw [hn]
  calc
    _ ≤ (1/y^2)*y^(1/4:ℝ)*(4*y^(1/4:ℝ)) := by gcongr
    _ = 4*y^(-3/2:ℝ) := by
      have hi : 1/y^2=y^(-2:ℝ) := by rw [Real.rpow_neg hy0.le];norm_num
      rw [hi]
      calc
        _ = 4*((y^(-2:ℝ)*y^(1/4:ℝ))*y^(1/4:ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hy0,← Real.rpow_add hy0];norm_num

lemma majorant_integrable : IntegrableOn majorant (Ioi (0:ℝ)) := by
  have h1 : IntegrableOn majorant (Ioc (0:ℝ) 1) := by
    apply (integrableOn_const (C:=(1:ℝ)) (s:=Ioc (0:ℝ) 1) (by simp)).congr_fun
      _ measurableSet_Ioc
    intro y hy
    simp [majorant,hy.2]
  have h2 : IntegrableOn majorant (Ioi (1:ℝ)) := by
    have hg : IntegrableOn (fun y : ℝ => 4*y^(-3/2:ℝ)) (Ioi (1:ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (show (-3/2:ℝ)< -1 by norm_num)
        (show (0:ℝ)<1 by norm_num)).const_mul 4
    apply hg.congr_fun _ measurableSet_Ioi
    intro y hy
    simp [majorant,(show 1<y from hy).not_ge]
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by ext x;simp
  rw [← hu]
  exact h1.union h2

/-- Actual coefficient extraction is justified by a uniform integrable majorant,
including the whole infinite tail; no finite grid or Mellin identity is assumed. -/
theorem regularized_hasDerivAt : HasDerivAt regularizedMellin
    (IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1) 0 := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Ioi (0:ℝ)))
    (F:=packet) (F':=packetDeriv) (bound:=majorant)
    (s:=Icc ((-1/4:ℝ)) (1/4))
    (Icc_mem_nhds (show (-1/4:ℝ)<0 by norm_num) (show (0:ℝ)<1/4 by norm_num))
    (Eventually.of_forall fun s => (packet_measurable s).aestronglyMeasurable)
    (show IntegrableOn (packet 0) (Ioi (0:ℝ)) volume from by
      have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by ext y;simp
      have hr : IntegrableOn (raw 0) (Ioi (0:ℝ)) volume := by
        rw [← hu]
        exact (raw_integrable_small (j:=0) (by norm_num)).union
          (raw_integrable_large (j:=0) (by norm_num))
      apply hr.congr_fun _ measurableSet_Ioi
      intro y hy
      simp [packet])
    (packetDeriv_measurable 0).aestronglyMeasurable
    (show ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ∀ s∈Icc ((-1/4:ℝ)) (1/4),
        ‖packetDeriv s y‖ ≤ majorant y from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      intro s hs
      by_cases hy1 : y≤1
      · simpa [majorant,hy1] using derivative_small hs.1 hy hy1
      · simpa [majorant,hy1] using derivative_large hs.2 (lt_of_not_ge hy1))
    majorant_integrable
    (ae_of_all _ fun y s hs => packet_derivative s y)
  have he : (∫ y in Ioi (0:ℝ), packetDeriv 0 y) =
      IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 := by
    unfold IEANTN.RHSmoothing.J
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have he := actual_eq_raw 1 hy
    change packetDeriv 0 y = BoxMellinInputs.v1.integrand 1 y
    rw [he]
    simp [packetDeriv,packet,raw]
    ring
  rw [he] at h
  exact h.2

#print axioms regularized_hasDerivAt
end RHOcticPush.BoxMellin
