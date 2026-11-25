import CompactDualSourceFirst

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.NewAudit
open RH080.Dual

theorem fixed_lower_kernel
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hc : Continuous F)
    (hpair : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hd : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) := by
  have hweak := weak_duality_l1 F G compactStep (36/11) (123/100)
    hF hG compactStep_integrable hc hpair (by norm_num)
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1)
    (fun v _ => (compactStep_bounds v).2)
    kernel_compact_global
  have h := RH080.Functional.ratio_lower_of_dual
    (by nlinarith) hd (by norm_num : (0 : ℝ) < 123/100) hweak
  norm_num at h
  exact h

theorem fixed_lower_source_linked
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hc : Continuous F)
    (hpair : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hd : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) := by
  have hweak := weak_duality_l1 F G compactStep (36/11) (123/100)
    hF hG compactStep_integrable hc hpair (by norm_num)
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1)
    (fun v _ => (compactStep_bounds v).2)
    source_first_compact_global
  have h := RH080.Functional.ratio_lower_of_dual
    (by nlinarith) hd (by norm_num : (0 : ℝ) < 123/100) hweak
  norm_num at h
  exact h

#print axioms fixed_lower_kernel
#print axioms fixed_lower_source_linked
#print axioms RH080.Dual.actual_source_first_functional_result
end RH080.NewAudit
