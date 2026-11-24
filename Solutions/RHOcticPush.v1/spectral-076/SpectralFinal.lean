import SpectralSourceTransport
import SpectralZeroEnvelope
import SpectralProfile

/-! Actual arithmetic compensation from genuine general integrated Perron and
Nicolas sources. The entire signed infinite-zero chain is consumed; no desired
J-error, finite truncation, numerical moment or GM envelope is assumed. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0

/-- Full nonconstant compensation function on the complete real ray. -/
theorem actual_compensation_profile (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {x : ℝ} (hx : Real.exp 24 ≤ x) :
    |RHOcticPush.GM.error x| ≤ profile (Real.log x) := by
  have hd := spectral_domain hx
  have hx0 : 0 < x := (Real.exp_pos 24).trans_le hx
  have hi := actual_source_transport hI (by norm_num : (1:ℝ)<3) hd.1
  have hz := actual_zero_envelope rh hN hI hx
  have hl : ‖(Real.log (2*Real.pi) : ℂ)*
      (∫ t in (3:ℝ)..x,(gmWeight t : ℂ))‖ ≤ 17/10 := by
    rw [intervalIntegral.integral_ofReal]
    exact actual_linear_integral_bound hd.1
  have ht := actual_trivial_integral_bound hd.1
  have he : |RHOcticPush.GM.error x-RHOcticPush.GM.error 3| ≤
      ‖weightedTransport 3 x (fun t => ∑' r,zeroPrimitive t r)‖+17/10+1/10 := by
    have hh := norm_add_le
      (-weightedTransport 3 x (fun t => ∑' r,zeroPrimitive t r)-
        (Real.log (2*Real.pi) : ℂ)*(∫ t in (3:ℝ)..x,(gmWeight t : ℂ)))
      (∫ t in (3:ℝ)..x,(IEANTN.RHSmoothing.trivial t : ℂ)*(gmWeight t : ℂ))
    have hh' := norm_sub_le
      (-weightedTransport 3 x (fun t => ∑' r,zeroPrimitive t r))
      ((Real.log (2*Real.pi) : ℂ)*(∫ t in (3:ℝ)..x,(gmWeight t : ℂ)))
    rw [←hi,Complex.norm_real,Real.norm_eq_abs] at hh
    rw [norm_neg] at hh'
    linarith
  have ha := actual_error_three
  have htri := abs_add_le (RHOcticPush.GM.error x-RHOcticPush.GM.error 3)
    (RHOcticPush.GM.error 3)
  simp only [sub_add_cancel] at htri
  unfold profile
  rw [Real.exp_half,Real.exp_log hx0]
  linarith

/-- The requested coefficient is now a conclusion for the actual arithmetic
observable, with the stronger onset exp24 and no additive fixed allowance. -/
theorem actual_compensation_076 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {x : ℝ} (hx : Real.exp 24 ≤ x) :
    |RHOcticPush.GM.error x| < (76/1000)*(Real.sqrt x/(Real.log x)^2) := by
  have hp := (actual_compensation_profile rh hN hI hx).trans_lt
    (profile_lt_076 (spectral_domain hx).2)
  simpa only [Real.exp_half,Real.exp_log ((Real.exp_pos 24).trans_le hx)] using hp

/-- A separate stronger coefficient on the original high-logarithm range,
using exactly the same full signed formula and source inputs. -/
theorem actual_compensation_055 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {x : ℝ} (hx : Real.exp 35 ≤ x) :
    |RHOcticPush.GM.error x| < (55/1000)*(Real.sqrt x/(Real.log x)^2) := by
  have h24 := (Real.exp_le_exp.mpr (by norm_num : (24:ℝ)≤35)).trans hx
  have h35 : (35:ℝ) ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 35) hx
  have hp := (actual_compensation_profile rh hN hI h24).trans_lt (profile_lt_055 h35)
  simpa only [Real.exp_half,Real.exp_log ((Real.exp_pos 35).trans_le hx)] using hp

#print axioms actual_compensation_profile
#print axioms actual_compensation_076
#print axioms actual_compensation_055
end RHOcticPush.Spectral076
