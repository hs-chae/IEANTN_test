import SpectralMassTransport
import SpectralResidual
import RemainderIntegral
import RemainderScalar

/-! Complete actual signed-zero envelope on the whole intended real ray. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHOcticPush.Convergence
set_option maxHeartbeats 0

lemma spectral_domain {x : ℝ} (hx : Real.exp 24 ≤ x) :
    3 ≤ x ∧ 24 ≤ Real.log x := by
  have he : (3 : ℝ) ≤ Real.exp 24 := by linarith [Real.add_one_le_exp (24 : ℝ)]
  refine ⟨he.trans hx,?_⟩
  have h := Real.log_le_log (Real.exp_pos 24) hx
  simpa only [Real.log_exp] using h

theorem actual_zero_envelope (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {x : ℝ} (hx : Real.exp 24 ≤ x) :
    ‖weightedTransport 3 x (fun t => ∑' r,zeroPrimitive t r)‖ ≤
      (104/125 : ℝ)+(47/1000)*(1+4/(Real.log x-8))*(Real.sqrt x/(Real.log x)^2) := by
  have hd := spectral_domain hx
  have hnorm := full_weighted_zero_bound rh hN hI (by norm_num : (1:ℝ)<3) hd.1
  have hbeta := RHLimit.NicolasMass.beta_lt_047.le
  have hU := squareAllowance_nonneg (by norm_num : (1:ℝ)<3) hd.1
  have hm := mul_le_mul_of_nonneg_left hbeta hU
  have hi := remainderIntegral_bound hx
  change (∫ t in (3:ℝ)..x,remainderKernel t) ≤
    8+2*Real.sqrt x/((Real.log x)^2*(Real.log x-8)) at hi
  have ha := zero_anchor_scalar
  have hh : (47/1000 : ℝ)*(1+4/(Real.log x-8))*(Real.sqrt x/(Real.log x)^2) =
      (47/1000)*(Real.sqrt x/(Real.log x)^2)+
        (47/1000)*4*Real.sqrt x/((Real.log x)^2*(Real.log x-8)) := by
    field_simp
    <;> ring
  rw [hh]
  unfold squareAllowance at hm hnorm
  have hz := hnorm.trans hm
  have hI := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2*(47/1000))
  ring_nf at hz hI ha ⊢
  nlinarith only [hz,hI,ha]

#print axioms spectral_domain
#print axioms actual_zero_envelope
end RHOcticPush.Spectral076
