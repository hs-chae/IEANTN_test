import SynergyAnalytic.HeightPNTInstance
import SynergyAnalytic.PrimeRichWidth
namespace SynergyAnalytic.HeightPoint
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 0

theorem source_prime_rich_017
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8))
    {x:ℝ} (hx:Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(17/1000:ℝ)*x^((7:ℝ)/8))-primeCounting x :=
  prime_rich_017_008442 (source_pi_008442 h hCHJ hrvm hsmall hlow hRH hQRH) hx

#print axioms source_prime_rich_017
end SynergyAnalytic.HeightPoint
