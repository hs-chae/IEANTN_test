/- Additive continuation of the campaign's later pure-kernel numerical checkpoint.
No claim that new272Gaussian/768height evidence was available at the initial baseline. -/
import SynergyAnalytic.PureKernelRationalProfile
import SynergyAnalytic.RationalPrimeRichFunction
namespace SynergyAnalytic.HeightPoint.PureKernelPrimeRichFunction
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem prime_rich_function
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+rationalRichWidth (8433850764/1000000000000) (Real.log x)*
        x^((7:ℝ)/8))-primeCounting x :=
  prime_rich_rational_function (by norm_num) rational_checkpoint_330
    (fun z hz=>PureKernelRationalProfile.pi_rational_point h hCHJ hrvm hsmall hlow hRH hQRH hz) hx

#print axioms prime_rich_function
end SynergyAnalytic.HeightPoint.PureKernelPrimeRichFunction
