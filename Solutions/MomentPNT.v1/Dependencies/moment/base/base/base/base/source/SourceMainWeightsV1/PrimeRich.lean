/- Downstream reuse of the actual C-weight conditional PNT theorem. -/
import SourceMainWeightsV1.PNT
import SynergyAnalytic.PrimeRichWidth
namespace SourceMainWeightsV1.PNT
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
open SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem source_prime_rich_actual_weights
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(17/1000:ℝ)*x^((7:ℝ)/8))-primeCounting x := by
  have hpi := source_pi_actual_weights h hCHJ hrvm hsmall hlow hRH hQRH
  have rounded : HasPowerLogBound Eπ (4221/500000) 0 (7/8) (Real.exp 330) := by
    intro y hy
    have hb := hpi y hy
    have hy0 : 0 < y := (Real.exp_pos 330).trans_le hy
    simp only [pow_zero,mul_one] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right (by norm_num :
      (8441646/1000000000:ℝ) ≤ 4221/500000) (by positivity))
  exact prime_rich_017_008442 rounded hx

end SourceMainWeightsV1.PNT
#print axioms SourceMainWeightsV1.PNT.source_prime_rich_actual_weights
