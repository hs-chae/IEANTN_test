/- Strong kernel-only comparator after sharing all new mathematical lemmas.
It verifies the same interval model and obtains the same PNT envelope, without
using a C source execution theorem or the source-prefix execution family. -/
import SynergyHeightC.MainModelOnlyCaps
import SynergyHeightC.MainRationalProfile
import SynergyAnalytic.RationalPNTTransfer
namespace SynergyHeightC.MainModelOnlyProfile
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem model_finite_sum_330 :
    2*(∑ i ∈ Finset.range logCellCount,
      ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
        pairedFactor (pointD i) (1/8) 330) ≤ 8433850764/1000000000000 := by
  have bounded := (actual_weight_sum_bound SourceMainWeightsV1.All.all_domains
    (out:=SourceMainWeightsV1.All.total) SourceMainWeightsV1.All.exact_total).trans
      SourceMainWeightsV1.PNT.actual_word_bound
  have form : (∑ i ∈ Finset.range logCellCount,realTerm i)=
      2*(∑ i ∈ Finset.range logCellCount,
        ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
          pairedFactor (pointD i) (1/8) 330) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i member
    simp only [realTerm,mul_assoc]
  rw [form] at bounded
  exact bounded

theorem model_rational_ray
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    {L : ℝ} (future : 330 ≤ L)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (rationalHeightCoefficient (8433850764/1000000000000) L)
      0 (7/8) (Real.exp L) :=
  pi_rational_ray_of_count_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    future MainRationalProfile.source_weights_nonnegative slopes model_finite_sum_330
    (MainModelOnlyCaps.model_actual_height_caps SourceMainWeightsV1.All.all_domains h hRH)
    h hCHJ hrvm hsmall hlow hRH hQRH

theorem model_rational_point
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*x^(-(1:ℝ)/8) :=
  pi_rational_point_of_count_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    hx MainRationalProfile.source_weights_nonnegative slopes model_finite_sum_330
    (MainModelOnlyCaps.model_actual_height_caps SourceMainWeightsV1.All.all_domains h hRH)
    h hCHJ hrvm hsmall hlow hRH hQRH

#print axioms model_finite_sum_330
#print axioms model_rational_ray
#print axioms model_rational_point
end SynergyHeightC.MainModelOnlyProfile
