/- Source-backed rational-profile consequences: shorter prime-rich intervals.
The same fourteen analytic inputs are retained; no new numerical premise is used. -/
import SynergyHeightC.MainRationalClosed
import SynergyAnalytic.PrimeRichWidth
namespace SynergyHeightC.MainPrimeRichRefined
open Real IEANTN SynergyAnalytic SynergyAnalytic.HeightPoint
open WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem prime_rich_capped {C x0 x width count : ℝ}
    (positiveC : 0 ≤ C) (source : HasPowerLogBound Eπ C 0 (7/8) x0)
    (positiveWidth : 0 ≤ width) (widthCap : width ≤ 9/500)
    (coefficient : count ≤ width/(1000001/1000000)-C*(5001/5000+1))
    (start : x0 ≤ x) (initial : Real.exp 330 ≤ x) :
    count*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+width*x^((7:ℝ)/8))-primeCounting x := by
  have rich := prime_rich_width_parameter positiveWidth widthCap positiveC source start initial
  have positiveX : 0 < x := (Real.exp_pos _).trans_le initial
  have oneX : 1 < x := (by norm_num : (1:ℝ)<100^8).trans_le
    (exp330_ge_power.trans initial)
  have logPositive : 0 < Real.log x := Real.log_pos oneX
  have weight : 0 ≤ x^((7:ℝ)/8)/Real.log x := by positivity
  have comparison := mul_le_mul_of_nonneg_right coefficient weight
  simp only [←mul_div_assoc] at comparison
  exact comparison.trans rich

theorem source_prime_rich_500
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 500 ≤ x) :
    (1/10000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(77/5000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have source := MainRationalClosed.source_pi_500 h hCHJ hrvm hsmall hlow hRH hQRH
  exact prime_rich_capped (by norm_num) source (by norm_num) (by norm_num)
    (by norm_num) hx ((Real.exp_le_exp.mpr (by norm_num : (330:ℝ)≤500)).trans hx)

theorem source_prime_rich_1000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 1000 ≤ x) :
    (7/100000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(141/10000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have source := MainRationalClosed.source_pi_1000 h hCHJ hrvm hsmall hlow hRH hQRH
  exact prime_rich_capped (by norm_num) source (by norm_num) (by norm_num)
    (by norm_num) hx ((Real.exp_le_exp.mpr (by norm_num : (330:ℝ)≤1000)).trans hx)

#print axioms prime_rich_capped
#print axioms source_prime_rich_500
#print axioms source_prime_rich_1000
end SynergyHeightC.MainPrimeRichRefined
