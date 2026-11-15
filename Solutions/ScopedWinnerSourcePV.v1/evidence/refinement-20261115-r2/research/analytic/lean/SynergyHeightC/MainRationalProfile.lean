/- Quantitative whole-function propagation of the unchanged source-verified C sum.
The finite actual slope range is explicit here and closed by the separate source
slope family in the final application, never assumed as a new analytic premise. -/
import SynergyHeightC.MainFinalTotal
import SynergyAnalytic.SourceCountProfile
import SynergyAnalytic.RationalHeightProperties
namespace SynergyHeightC.MainRationalProfile
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem source_weights_nonnegative (i : Nat) (hi : i < logCellCount) :
    0 ≤ (1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i := by
  have domain := (domain_spec (i:=i) (SourceMainWeightsV1.All.all_domains i hi)).2.2.2
  have cInteger : 0 ≤ (adjustedC (modelPair i).1).hi := domain.2.2.2.2.2.2.1
  have cReal : 0 ≤ fullC i := by
    change 0 ≤ ((adjustedC (modelPair i).1).hi:ℝ)/(ProofBox.scale 128:ℝ)
    exact div_nonneg (by exact_mod_cast cInteger) (RealBox.scale_real_pos 128).le
  have heightPositive : 0 < heightEndpoint i := Real.exp_pos _
  have weight := sub_nonneg.mpr (one_div_le_one_div_of_le heightPositive
    (heightEndpoint_monotone (Nat.le_succ i)))
  exact mul_nonneg weight cReal

theorem source_finite_sum_330 :
    2*(∑ i ∈ Finset.range logCellCount,
      ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
        pairedFactor (pointD i) (1/8) 330) ≤ 8433850764/1000000000000 := by
  have bounded := (actual_weight_sum_bound SourceMainWeightsV1.All.all_domains
    (out:=SourceMainBudgetV1.Data.total 768) (MainBudgetSourceSum.prefix_value 768 (by decide))).trans
      MainFinalTotal.source_total_word_bound
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

theorem source_ray_rational_bound
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    {L : ℝ} (future : 330 ≤ L) :
    rayCoefficient heightEndpoint fullC pointD logCellCount L ≤
      rationalHeightCoefficient (8433850764/1000000000000) L :=
  ray_rational_bound source_weights_nonnegative slopes source_finite_sum_330 future

theorem pi_rational_ray
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    {L : ℝ} (future : 330 ≤ L)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (rationalHeightCoefficient (8433850764/1000000000000) L)
      0 (7/8) (Real.exp L) := by
  have caps := source_actual_height_caps MainFinalTotal.actual_running_source_family
    SourceMainWeightsV1.All.all_domains h hRH
  have source := source_pi_count_profile_ray heightEndpoint_monotone heightEndpoint_zero
    heightEndpoint_last h caps hCHJ hrvm hsmall hlow hRH hQRH future
  have budget := source_ray_rational_bound slopes future
  intro x hx
  have positive : 0 < x := (Real.exp_pos L).trans_le hx
  have value := source x hx
  simp only [pow_zero,mul_one] at value ⊢
  exact value.trans (mul_le_mul_of_nonneg_right budget (by positivity))

theorem pi_rational_point
    (slopes : ∀ i < logCellCount, 77 ≤ pointD i ∧ pointD i ≤ 163)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    Eπ x ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log x)*
      x^(-(1:ℝ)/8) := by
  have hx0 : 0 < x := (Real.exp_pos 330).trans_le hx
  have future : 330 ≤ Real.log x := by
    have bound := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using bound
  have value := pi_rational_ray slopes future h hCHJ hrvm hsmall hlow hRH hQRH x
    (by rw [Real.exp_log hx0])
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using value

#print axioms source_weights_nonnegative
#print axioms source_finite_sum_330
#print axioms source_ray_rational_bound
#print axioms pi_rational_ray
#print axioms pi_rational_point
end SynergyHeightC.MainRationalProfile
