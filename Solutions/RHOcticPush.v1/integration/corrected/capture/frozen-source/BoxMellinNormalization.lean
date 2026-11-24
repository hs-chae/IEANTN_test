import BoxMellinBridge

namespace RHOcticPush.BoxMellin
open Real MeasureTheory Set RHOcticPush.Box
set_option maxHeartbeats 0

noncomputable def mellinPacket (s y : ℝ) : ℝ := abs (Real.sin y/y) * y^(s-1)
noncomputable def mellin (s : ℝ) : ℝ := ∫ y in Ioi (0:ℝ), mellinPacket s y
noncomputable def cutoffPacket (s y : ℝ) : ℝ := if y≤1 then y^(s-1) else 0

lemma mellinPacket_continuous (s : ℝ) : ContinuousOn (mellinPacket s) (Ioi (0:ℝ)) := by
  exact ((Real.continuous_sin.continuousOn.div continuousOn_id
    (fun y hy => (show 0<y from hy).ne')).abs).mul
    (continuousOn_id.rpow_const (fun y hy => Or.inl (show 0<y from hy).ne'))

lemma mellinPacket_small {s y : ℝ} (hy : 0<y) :
    ‖mellinPacket s y‖ ≤ y^(s-1) := by
  have hh : |Real.sin y/y| ≤ 1 := by
    rw [abs_div,abs_of_pos hy]
    exact (div_le_one hy).mpr (by simpa [abs_of_pos hy] using Real.abs_sin_le_abs (x:=y))
  have hp := Real.rpow_nonneg hy.le (s-1)
  simpa [mellinPacket,norm_mul,Real.norm_eq_abs,abs_of_nonneg hp] using
    mul_le_mul_of_nonneg_right hh hp

lemma mellinPacket_large {s y : ℝ} (hy : 1<y) :
    ‖mellinPacket s y‖ ≤ y^(s-2) := by
  have hy0 : 0<y := by linarith
  have hh : |Real.sin y/y| ≤ 1/y := by
    rw [abs_div,abs_of_pos hy0]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) hy0.le
  have hp := Real.rpow_nonneg hy0.le (s-1)
  have h := mul_le_mul_of_nonneg_right hh hp
  have he : (1/y)*y^(s-1)=y^(s-2) := by
    have hi : 1/y=y^(-1:ℝ) := by rw [Real.rpow_neg hy0.le,Real.rpow_one];simp
    rw [hi,← Real.rpow_add hy0]
    congr 1
    ring
  rw [he] at h
  simpa [mellinPacket,norm_mul,Real.norm_eq_abs,abs_of_nonneg hp] using h

/-- Absolute convergence on the entire genuine Mellin strip0<s<1. -/
theorem mellin_integrable {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    IntegrableOn (mellinPacket s) (Ioi (0:ℝ)) := by
  have hi : IntegrableOn (fun y : ℝ => y^(s-1)) (Ioc (0:ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by norm_num)).mpr
      (by linarith)
  have h1 : IntegrableOn (mellinPacket s) (Ioc (0:ℝ) 1) := by
    have hc : ContinuousOn (mellinPacket s) (Ioc (0:ℝ) 1) :=
      (mellinPacket_continuous s).mono (by intro y hy;exact hy.1)
    apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact mellinPacket_small hy.1
  have hi2 : IntegrableOn (fun y : ℝ => y^(s-2)) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have h2 : IntegrableOn (mellinPacket s) (Ioi (1:ℝ)) := by
    have hc : ContinuousOn (mellinPacket s) (Ioi (1:ℝ)) :=
      (mellinPacket_continuous s).mono (by intro y hy;change 0<y;have h:1<y:=hy;linarith)
    apply hi2.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mellinPacket_large hy
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by ext y;simp
  rw [← hu]
  exact h1.union h2

lemma cutoff_integrable {s : ℝ} (hs0 : 0<s) :
    IntegrableOn (cutoffPacket s) (Ioi (0:ℝ)) := by
  have hi : IntegrableOn (fun y : ℝ => y^(s-1)) (Ioc (0:ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by norm_num)).mpr
      (by linarith)
  have h1 : IntegrableOn (cutoffPacket s) (Ioc (0:ℝ) 1) := by
    exact hi.congr_fun (fun y hy => by simp [cutoffPacket,hy.2]) measurableSet_Ioc
  have h2 : IntegrableOn (cutoffPacket s) (Ioi (1:ℝ)) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi (1:ℝ)) volume).congr_fun
      _ measurableSet_Ioi
    intro y hy
    simp [cutoffPacket,(show 1<y from hy).not_ge]
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by ext y;simp
  rw [← hu]
  exact h1.union h2

lemma cutoff_integral {s : ℝ} (hs0 : 0<s) :
    (∫ y in Ioi (0:ℝ), cutoffPacket s y)=1/s := by
  have he : cutoffPacket s = (Iic (1:ℝ)).indicator (fun y : ℝ => y^(s-1)) := rfl
  rw [he,setIntegral_indicator measurableSet_Iic]
  have hset : Ioi (0:ℝ) ∩ Iic 1 = Ioc 0 1 := by ext y;rfl
  rw [hset,← intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    integral_rpow (Or.inl (show -1<s-1 by linarith))]
  simp [Real.zero_rpow hs0.ne',hs0.ne',sub_add_cancel]

lemma packet_sub_cutoff (s : ℝ) {y : ℝ} (hy : 0<y) :
    packet s y=mellinPacket s y-cutoffPacket s y := by
  have he : Real.exp (s*Real.log y)=y^s := by rw [Real.rpow_def_of_pos hy];congr 1;ring
  unfold packet raw mellinPacket cutoffPacket
  simp only [pow_zero,mul_one,he]
  simp only [Real.rpow_sub hy,Real.rpow_one]
  split_ifs <;> ring

/-- The actual full Mellin integral has pole1/s and the proved regularized part. -/
theorem mellin_renormalized {s : ℝ} (hs0 : 0<s) (hs1 : s<1) :
    mellin s=1/s+regularizedMellin s := by
  have he : regularizedMellin s=mellin s-1/s := by
    unfold regularizedMellin mellin
    calc
      _ = ∫ y in Ioi (0:ℝ), mellinPacket s y-cutoffPacket s y :=
        setIntegral_congr_fun measurableSet_Ioi (fun y hy => packet_sub_cutoff s hy)
      _ = _ := by rw [integral_sub (mellin_integrable hs0 hs1) (cutoff_integrable hs0),
        cutoff_integral hs0]
  linarith

/-- Exact constant normalization, separate from evaluating it aslog2. -/
theorem regularized_zero : regularizedMellin 0=
    IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 := by
  unfold regularizedMellin IEANTN.RHSmoothing.J
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have he := actual_eq_raw 0 hy
  change packet 0 y=BoxMellinInputs.v1.integrand 0 y
  rw [he]
  simp [packet]

#print axioms mellin_integrable
#print axioms mellin_renormalized
#print axioms regularized_zero
end RHOcticPush.BoxMellin
