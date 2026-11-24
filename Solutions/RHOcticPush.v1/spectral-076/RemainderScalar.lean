import AnchorScalar

/-! Corrected scalar budget using the valid b=8 antiderivative.
The earlier b=6 scalar statement remains true but its proposed antiderivative
has derivative below the integrand and cannot supply the required analytic bound. -/
namespace RHOcticPush.Spectral076
open Real
set_option maxHeartbeats 0

theorem spectral_scalar_budget_eight {L : ℝ} (hL : 24 ≤ L) :
    (24/5 : ℝ) + (47/1000)*(1+4/(L-8))*(Real.exp (L/2)/L^2) <
      (76/1000)*(Real.exp (L/2)/L^2) := by
  have h0 : 0 < L-8 := by linarith
  have hf : 4/(L-8) ≤ (1/4 : ℝ) := by
    apply (div_le_iff₀ h0).mpr
    linarith
  have hE := exp_square_ratio_lower hL
  have he : 0 ≤ Real.exp (L/2)/L^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (show (47/1000 : ℝ)*(1+4/(L-8)) ≤ (47/1000)*(5/4) by linarith) he
  linarith

#print axioms spectral_scalar_budget_eight
end RHOcticPush.Spectral076
