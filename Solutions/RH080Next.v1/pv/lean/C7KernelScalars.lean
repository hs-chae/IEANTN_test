import WindowInputBounds
import WindowPositiveArea
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.PosthocKernelControl
open RH080Next.Explicit RH080Next.Primal RH080Next.ScalarInputBounds
open RH080Next.ScalarPositiveArea

theorem qMassA0_checked : qMassA0 WindowPV.Data.affineNodes 360 ≤ (2 : ℚ) :=
  WindowPV.actual_qMassA0

theorem qV0_checked : qV0 WindowPV.Data.affineNodes =
    (14033179036371096 : ℚ)/10000000000000000 := WindowPV.actual_qV0

theorem coefficients_checked : WindowPV.Data.affineNodes.all
    (fun a => decide (|a| ≤ (1 : ℚ))) = true := WindowPV.actual_input_coefficients

theorem positiveArea_checked : qPositiveArea WindowPV.Data.affineNodes 360 ≤
    (73712934591273687 : ℚ)/(360*10000000000000000) := WindowPV.actual_qPositiveArea

theorem positive_leak_checked :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum WindowPV.Data.affineNodes 360) ≤
      (73712934591273687 : ℝ)/(360*10000000000000000) := by
  have hlen : 2 ≤ WindowPV.Data.affineNodes.length := by
    rw [WindowPV.Data.affineNodes_length]
    norm_num
  have hlast : node WindowPV.Data.affineNodes
      (WindowPV.Data.affineNodes.length - 1) = 0 := by
    unfold node WindowPV.Data.affineNodes
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    norm_num
  rw [positiveLeak_affineSpectrum_eq_nodalPositiveArea WindowPV.Data.affineNodes 360
    hlen (by norm_num) (by rw [WindowPV.Data.affineNodes_length]; norm_num) hlast]
  have hq : (qPositiveArea WindowPV.Data.affineNodes 360 : ℝ) ≤
      (((73712934591273687 : ℚ)/(360*10000000000000000) : ℚ) : ℝ) := by
    exact_mod_cast positiveArea_checked
  rw [qPositiveArea_cast] at hq
  convert hq using 1 <;> norm_num

theorem scalar_caps :
    (999999999/1000000000 : ℝ) ≤ nodalF0 WindowPV.Data.affineNodes 360 ∧
    nodalMassA0 WindowPV.Data.affineNodes 360 ≤ 2 ∧
    nodalV0 WindowPV.Data.affineNodes ≤ 10 ∧
    nodalV1 WindowPV.Data.affineNodes 360 ≤ (509/125 : ℝ) ∧
    nodalMu2Upper WindowPV.Data.affineNodes 360 ≤ (249/1000 : ℝ) ∧
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum WindowPV.Data.affineNodes 360) ≤
      (2559477/125000000 : ℝ) ∧
    nodalH WindowPV.Data.affineNodes 360 ≤ (14327/125000 : ℝ) ∧
    ∀ v : ℝ, |affineSpectrum WindowPV.Data.affineNodes 360 v| ≤ 1 := by
  have hf : nodalF0 WindowPV.Data.affineNodes 360 =
      (3599999999999999998 : ℝ)/(360*10000000000000000) := by
    rw [← WindowPV.qF0_cast, WindowPV.actual_qF0]
    norm_num
  have hh : nodalH WindowPV.Data.affineNodes 360 =
      (1146154494119977 : ℝ)/10000000000000000 := by
    rw [← WindowPV.qH_cast, WindowPV.actual_qH]
    norm_num
  have hv : nodalV1 WindowPV.Data.affineNodes 360 =
      (40713308729275680 : ℝ)/10000000000000000 := by
    rw [← WindowPV.qV1_cast, WindowPV.actual_qV1]
    norm_num
  have hmu : nodalMu2Upper WindowPV.Data.affineNodes 360 ≤
      (69452659995205718 : ℝ)/(6*360^3*1000000000) := by
    have hq : (WindowPV.qMu2 WindowPV.Data.affineNodes 360 : ℝ) ≤
        (((69452659995205718 : ℚ)/(6*360^3*1000000000) : ℚ) : ℝ) := by
      exact_mod_cast WindowPV.actual_qMu2
    rw [WindowPV.qMu2_cast] at hq
    convert hq using 1 <;> norm_num
  have hm : nodalMassA0 WindowPV.Data.affineNodes 360 ≤ 2 := by
    have h : (qMassA0 WindowPV.Data.affineNodes 360 : ℝ) ≤ 2 := by
      exact_mod_cast qMassA0_checked
    simpa only [qMassA0_cast] using h
  have hv0 : nodalV0 WindowPV.Data.affineNodes =
      (14033179036371096 : ℝ)/10000000000000000 := by
    rw [← qV0_cast, qV0_checked]
    norm_num
  have hw (v : ℝ) : |affineSpectrum WindowPV.Data.affineNodes 360 v| ≤ 1 := by
    apply RH080Next.Primal.affineSpectrum_abs_le _ _ _
      (by rw [WindowPV.Data.affineNodes_length]; norm_num) (by norm_num)
    intro j hj
    have hall : ∀ a ∈ WindowPV.Data.affineNodes, |a| ≤ (1 : ℚ) := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using coefficients_checked
    simpa only [Rat.cast_one] using node_abs_bound _ _ hall j (by omega)
  refine ⟨?_, hm, ?_, ?_, ?_, ?_, ?_, hw⟩
  · rw [hf]; norm_num
  · rw [hv0]; norm_num
  · rw [hv]; norm_num
  · exact hmu.trans (by norm_num)
  · exact positive_leak_checked.trans (by norm_num)
  · rw [hh]; norm_num

#print axioms scalar_caps

end RH080Next.PosthocKernelControl
