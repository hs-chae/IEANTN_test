import CompactDualVerified

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Submission
open RH080.Dual

theorem l1_floor
    (F G : ℝ → ℝ) (hF : Integrable F) (hG : Integrable G) (hc : Continuous F)
    (hf : 𝓕 (fun x : ℝ => (F x : ℂ)) = fun v : ℝ => (G v : ℂ))
    (hden : 0 < F 0 - (36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) :
    (100/123 : ℝ) ≤ (∫ x : ℝ, |F x|) /
      (F 0 - (36/11 : ℝ)*(∫ v in exterior, max 0 (G v))) := by
  have hw := weak_duality_l1 F G compactStep (36/11) (123/100)
    hF hG compactStep_integrable hc hf (by norm_num)
    (fun v hv => compactStep_center v (le_of_not_gt hv))
    (fun v _ => (compactStep_bounds v).1) (fun v _ => (compactStep_bounds v).2)
    kernel_compact_global
  have hp : (0 : ℝ) < 123 / 100 := by norm_num
  have hm : 0 < (∫ x : ℝ, |F x|) := by
    by_contra! hm
    have hh := mul_nonpos_of_nonneg_of_nonpos hp.le hm
    linarith
  simpa using RH080.Functional.ratio_lower_of_dual hm hden hp hw

#print axioms l1_floor
#print axioms kernel_compact_obstruction
end RH080.Submission
