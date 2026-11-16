/- A full-function prime-rich conclusion from the proved rational PNT envelope.
It retains the old onset and count, while narrowing the interval for every x. -/
import SynergyAnalytic.RationalHeightProperties
import SynergyAnalytic.PrimeRichWidth
namespace SynergyAnalytic
open Real IEANTN
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable def rationalRichWidth (C L : ℝ) : ℝ :=
  (1000001/1000000)*(rationalHeightCoefficient C L*(5001/5000+1)+57/500000)

theorem rationalRichWidth_nonnegative {C L : ℝ} (hC : 0 ≤ C) (future : 330 ≤ L) :
    0 ≤ rationalRichWidth C L := by
  have coefficient := rationalHeightCoefficient_nonnegative hC future
  unfold rationalRichWidth
  positivity

theorem rationalRichWidth_smaller {C L : ℝ} (hC : 0 ≤ C)
    (initial : rationalHeightCoefficient C 330 < 8441646/1000000000)
    (future : 330 ≤ L) : rationalRichWidth C L < 17/1000 := by
  have coefficient := (rationalHeightCoefficient_antitone hC le_rfl future).trans_lt initial
  unfold rationalRichWidth
  nlinarith

theorem rationalRichWidth_antitone {C K L : ℝ} (hC : 0 ≤ C)
    (domain : 330 ≤ K) (future : K ≤ L) :
    rationalRichWidth C L ≤ rationalRichWidth C K := by
  have coefficient := rationalHeightCoefficient_antitone hC domain future
  unfold rationalRichWidth
  nlinarith

theorem rationalRichWidth_count_identity (C L : ℝ) :
    rationalRichWidth C L/(1000001/1000000)-
      rationalHeightCoefficient C L*(5001/5000+1)=57/500000 := by
  unfold rationalRichWidth
  ring

theorem rational_local_power_bound {C x : ℝ} (hC : 0 ≤ C)
    (profile : ∀ z ≥ Real.exp 330,
      Eπ z ≤ rationalHeightCoefficient C (Real.log z)*z^(-(1:ℝ)/8))
    (hx : Real.exp 330 ≤ x) :
    HasPowerLogBound Eπ (rationalHeightCoefficient C (Real.log x)) 0 (7/8) x := by
  have positiveX : 0 < x := (Real.exp_pos 330).trans_le hx
  have logX : 330 ≤ Real.log x := by
    have compared := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using compared
  intro z hz
  have positiveZ : 0 < z := positiveX.trans_le hz
  have logZ : Real.log x ≤ Real.log z := Real.log_le_log positiveX hz
  have coefficient := rationalHeightCoefficient_antitone hC logX logZ
  have value := (profile z (hx.trans hz)).trans
    (mul_le_mul_of_nonneg_right coefficient (Real.rpow_nonneg positiveZ.le _))
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using value

theorem prime_rich_rational_function {C x : ℝ} (hC : 0 ≤ C)
    (initial : rationalHeightCoefficient C 330 < 8441646/1000000000)
    (profile : ∀ z ≥ Real.exp 330,
      Eπ z ≤ rationalHeightCoefficient C (Real.log z)*z^(-(1:ℝ)/8))
    (hx : Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+rationalRichWidth C (Real.log x)*x^((7:ℝ)/8))-primeCounting x := by
  have logX : 330 ≤ Real.log x := by
    have compared := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using compared
  have widthCap := rationalRichWidth_smaller hC initial logX
  have rich := prime_rich_width_parameter (rationalRichWidth_nonnegative hC logX)
    (widthCap.le.trans (by norm_num : (17/1000:ℝ)≤9/500))
    (rationalHeightCoefficient_nonnegative hC logX)
    (rational_local_power_bound hC profile hx) le_rfl hx
  rw [rationalRichWidth_count_identity] at rich
  exact rich

theorem rationalRichWidth_checkpoint_330 :
    rationalRichWidth (8433850764/1000000000000) 330 < 16999/1000000 := by
  norm_num [rationalRichWidth,rationalHeightCoefficient,contractionFactor]

theorem rationalRichWidth_checkpoint_500 :
    rationalRichWidth (8433850764/1000000000000) 500 < 15414/1000000 := by
  norm_num [rationalRichWidth,rationalHeightCoefficient,contractionFactor]

theorem rationalRichWidth_checkpoint_1000 :
    rationalRichWidth (8433850764/1000000000000) 1000 < 14136/1000000 := by
  norm_num [rationalRichWidth,rationalHeightCoefficient,contractionFactor]

theorem rationalRichWidth_checkpoint_1000000 :
    rationalRichWidth (8433850764/1000000000000) 1000000 < 13057/1000000 := by
  norm_num [rationalRichWidth,rationalHeightCoefficient,contractionFactor]

#print axioms rationalRichWidth_nonnegative
#print axioms rationalRichWidth_smaller
#print axioms rationalRichWidth_antitone
#print axioms rationalRichWidth_count_identity
#print axioms rational_local_power_bound
#print axioms prime_rich_rational_function
#print axioms rationalRichWidth_checkpoint_330
#print axioms rationalRichWidth_checkpoint_500
#print axioms rationalRichWidth_checkpoint_1000
#print axioms rationalRichWidth_checkpoint_1000000
end SynergyAnalytic
