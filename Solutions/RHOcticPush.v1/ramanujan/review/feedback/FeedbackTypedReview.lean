import FeedbackCorollary
namespace RHOcticPush.FeedbackReview
open Real IEANTN
example (rh : RH.v1.hypothesis) (hi : IntegratedPerron.v1.formula)
    (hn : Nicolas.v1.spectral_bound) (hb : BPTOffOrdinate.v1.bound)
    {x : ℝ} (hx : Real.exp 35 ≤ x) :
    |primeCounting x-IEANTN.Li x| ≤
      PrimeSquareFeedback.envelope BoxTail.improvedBound (Real.log x) :=
  PrimeSquareFeedback.actual_box_pi_canonical rh hi hn hb hx
example (rh : RH.v1.hypothesis) (hi : IntegratedPerron.v1.formula)
    (hn : Nicolas.v1.spectral_bound) (hb : BPTOffOrdinate.v1.bound)
    {x : ℝ} (hx : Real.exp 100 ≤ x) :
    |primeCounting x-IEANTN.Li x| <
      Real.sqrt x*(Real.log x/(8*Real.pi)-(21/50)) :=
  PrimeSquareFeedback.actual_box_pi_clean_canonical rh hi hn hb hx
example {L : ℝ} (h : 100 ≤ L) (f : ℝ → ℝ) :
    (167/100 : ℝ)*Real.exp (L/2)/L <
      Spectral076.piEnvelope f L-PrimeSquareFeedback.envelope f L :=
  PrimeSquareFeedback.envelope_strict_gain h f

#print axioms RHOcticPush.PrimeSquareFeedback.box_polynomial_upper
#print axioms RHOcticPush.PrimeSquareFeedback.J_error_small
#print axioms RHOcticPush.PrimeSquareFeedback.li_upper
#print axioms RHOcticPush.PrimeSquareFeedback.J_upper_log
#print axioms RHOcticPush.PrimeSquareFeedback.prime_counting_upper_full_log
#print axioms RHOcticPush.PrimeSquareFeedback.Jupper_simplified
#print axioms RHOcticPush.PrimeSquareFeedback.prime_counting_upper_log
#print axioms RHOcticPush.PrimeSquareFeedback.prime_counting_upper
#print axioms RHOcticPush.PrimeSquareFeedback.actual_square_term
#print axioms RHOcticPush.PrimeSquareFeedback.actual_remainder_feedback
#print axioms RHOcticPush.PrimeSquareFeedback.remainder_gain
#print axioms RHOcticPush.PrimeSquareFeedback.coefficient_lower
#print axioms RHOcticPush.PrimeSquareFeedback.remainder_strict_gain
#print axioms RHOcticPush.PrimeSquareFeedback.actual_remainder_raw
#print axioms RHOcticPush.PrimeSquareFeedback.actual_remainder_effective
#print axioms RHOcticPush.PrimeSquareFeedback.effective_le_old
#print axioms RHOcticPush.PrimeSquareFeedback.effective_le_raw
#print axioms RHOcticPush.PrimeSquareFeedback.raw_lt_simplified
#print axioms RHOcticPush.PrimeSquareFeedback.effective_lt_simplified
#print axioms RHOcticPush.PrimeSquareFeedback.effective_strict_gain
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_le_old
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_eq_old
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_le_raw
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_eq_min
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_lt_simplified
#print axioms RHOcticPush.PrimeSquareFeedback.simplified_envelope_gain
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_strict_gain
#print axioms RHOcticPush.PrimeSquareFeedback.actual_pi_feedback
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_pi_log
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_pi
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_interval
#print axioms RHOcticPush.PrimeSquareFeedback.simplified_envelope_upper
#print axioms RHOcticPush.PrimeSquareFeedback.box_feedback_budget
#print axioms RHOcticPush.PrimeSquareFeedback.envelope_clean
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_pi_clean
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_pi_canonical
#print axioms RHOcticPush.PrimeSquareFeedback.actual_box_pi_clean_canonical
#print axioms RHOcticPush.PrimeSquareFeedback.clean_gain
#print axioms RHOcticPush.PrimeSquareFeedback.full_function_at100
end RHOcticPush.FeedbackReview
