/- Strongest shared-math kernel-only comparator using the pre-existing463-source
algorithm and frozen numerical words, with no C source proof imports. -/
import SynergyAnalytic.PureKernelHeightGuards
import SynergyAnalytic.RationalPNTTransfer
import SynergyAnalytic.PrimeRichWidth
namespace SynergyAnalytic.HeightPoint.PureKernelRationalProfile
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem pi_rational_ray {L : ℝ} (future : 330 ≤ L)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (rationalHeightCoefficient (8433850764/1000000000000) L)
      0 (7/8) (Real.exp L) :=
  pi_rational_ray_of_count_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    future PureKernelHeightGuards.weights_nonnegative
    (fun i hi=>PureKernelHeightGuards.slope_range hi) finite_height_budget_tight
    (actual_height_cells h hRH) h hCHJ hrvm hsmall hlow hRH hQRH

theorem pi_rational_point
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) :=
  pi_rational_point_of_count_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    hx PureKernelHeightGuards.weights_nonnegative
    (fun i hi=>PureKernelHeightGuards.slope_range hi) finite_height_budget_tight
    (actual_height_cells h hRH) h hCHJ hrvm hsmall hlow hRH hQRH

theorem pi_capped {L cap : ℝ} (future : 330 ≤ L)
    (checked : rationalHeightCoefficient (8433850764/1000000000000) L ≤ cap)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ cap 0 (7/8) (Real.exp L) := by
  have ray := pi_rational_ray future h hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have positive : 0 < x := (Real.exp_pos L).trans_le hx
  have value := ray x hx
  simp only [pow_zero,mul_one] at value ⊢
  exact value.trans (mul_le_mul_of_nonneg_right checked (by positivity))

theorem pi_500
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ (7648883/1000000000) 0 (7/8) (Real.exp 500) :=
  pi_capped (by norm_num) rational_checkpoint_500.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem pi_1000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ (7010158/1000000000) 0 (7/8) (Real.exp 1000) :=
  pi_capped (by norm_num) rational_checkpoint_1000.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem pi_1000000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ (6470481/1000000000) 0 (7/8) (Real.exp 1000000) :=
  pi_capped (by norm_num) rational_checkpoint_1000000.le h hCHJ hrvm hsmall hlow hRH hQRH

theorem rich_of_cap {C x0 x width count : ℝ}
    (positiveC : 0 ≤ C) (bound : HasPowerLogBound Eπ C 0 (7/8) x0)
    (positiveWidth : 0 ≤ width) (widthCap : width ≤ 9/500)
    (coefficient : count ≤ width/(1000001/1000000)-C*(5001/5000+1))
    (start : x0 ≤ x) (initial : Real.exp 330 ≤ x) :
    count*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+width*x^((7:ℝ)/8))-primeCounting x := by
  have rich := prime_rich_width_parameter positiveWidth widthCap positiveC bound start initial
  have positiveX : 0 < x := (Real.exp_pos _).trans_le initial
  have oneX : 1 < x := (by norm_num : (1:ℝ)<100^8).trans_le
    (exp330_ge_power.trans initial)
  have logPositive : 0 < Real.log x := Real.log_pos oneX
  have weight : 0 ≤ x^((7:ℝ)/8)/Real.log x := by positivity
  have comparison := mul_le_mul_of_nonneg_right coefficient weight
  simp only [←mul_div_assoc] at comparison
  exact comparison.trans rich

theorem prime_rich_500
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 500 ≤ x) :
    (1/10000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(77/5000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have bound := pi_500 h hCHJ hrvm hsmall hlow hRH hQRH
  exact rich_of_cap (by norm_num) bound (by norm_num) (by norm_num) (by norm_num)
    hx ((Real.exp_le_exp.mpr (by norm_num : (330:ℝ)≤500)).trans hx)

theorem prime_rich_1000
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 1000 ≤ x) :
    (7/100000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(141/10000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have bound := pi_1000 h hCHJ hrvm hsmall hlow hRH hQRH
  exact rich_of_cap (by norm_num) bound (by norm_num) (by norm_num) (by norm_num)
    hx ((Real.exp_le_exp.mpr (by norm_num : (330:ℝ)≤1000)).trans hx)

#print axioms pi_rational_ray
#print axioms pi_rational_point
#print axioms pi_capped
#print axioms pi_500
#print axioms pi_1000
#print axioms pi_1000000
#print axioms rich_of_cap
#print axioms prime_rich_500
#print axioms prime_rich_1000
end SynergyAnalytic.HeightPoint.PureKernelRationalProfile
