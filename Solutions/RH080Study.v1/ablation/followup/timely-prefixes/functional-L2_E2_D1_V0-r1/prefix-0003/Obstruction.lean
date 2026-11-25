import CompactDualVerified

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

theorem uniform_quotient_floor
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hcont : Continuous F)
    (hfourier : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hden : 0 < F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
      (F 0-(36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) := by
  have hweak := weak_duality_l1 F G compactStep (36/11) (123/100)
    hF hG compactStep_integrable hcont hfourier (by norm_num)
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1) (fun v _ => (compactStep_bounds v).2)
    kernel_compact_global
  rw [show (100/123 : ℝ) = 1/(123/100) by norm_num]
  exact RH080.Functional.ratio_lower_of_dual (by nlinarith) hden (by norm_num) hweak

#print axioms uniform_quotient_floor

#print axioms kernel_compact_obstruction
#print axioms kernel_compact_global
end RH080.Dual
