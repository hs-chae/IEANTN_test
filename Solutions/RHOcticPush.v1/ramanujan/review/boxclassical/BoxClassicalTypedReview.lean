import BoxClassicalCorollary
namespace RHOcticPush.BoxClassicalReview
open Real IEANTN
example (rh : RH.v1.hypothesis) (hi : IntegratedPerron.v1.formula)
    (hn : Nicolas.v1.spectral_bound) (hb : BPTOffOrdinate.v1.bound)
    {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| < Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) :=
  SpectralCorollary.actual_box_pi_ray_canonical rh hi hn hb hx
example (x : ℝ) : Real.sqrt x*(Real.log x/(8*Real.pi)-(1/3))-
    Real.sqrt x*(Real.log x/(8*Real.pi)-(2/5)) = Real.sqrt x/15 :=
  SpectralCorollary.clean_subtractive_gain x

#print axioms RHOcticPush.SpectralCorollary.whole_envelope_upper
#print axioms RHOcticPush.SpectralCorollary.box_quadratic_budget
#print axioms RHOcticPush.SpectralCorollary.whole_box_stronger_classical
#print axioms RHOcticPush.SpectralCorollary.actual_box_pi_log
#print axioms RHOcticPush.SpectralCorollary.actual_box_pi_ray
#print axioms RHOcticPush.SpectralCorollary.actual_box_pi_ray_canonical
#print axioms RHOcticPush.SpectralCorollary.clean_subtractive_gain
#print axioms RHOcticPush.SpectralCorollary.clean_subtractive_strict
#print axioms RHOcticPush.SpectralCorollary.clean_coefficient_at100
#print axioms RHOcticPush.SpectralCorollary.old_clean_coefficient_at100
#print axioms RHOcticPush.SpectralCorollary.normalized_point100
#print axioms RHOcticPush.SpectralCorollary.full_function_at100
end RHOcticPush.BoxClassicalReview
