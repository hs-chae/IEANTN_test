/- The actual C-expression sum, rather than the older survival-power enclosure,
supplies the finite numerical bound in the original conditional ANT consumer. -/
import SynergyHeightC.MainWeightSourceCaps
import SynergyHeightC.MainWeightSumSound
import SynergyAnalytic.HeightBudgetTransfer
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.PointExecuteAPI Real IEANTN WinnerOriginalScalars
open WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem prefixSum_function_exact : prefixSum=block 0 := by rfl

theorem actual_weight_sum_bound (domains : ∀ i < logCellCount, cellDomain i=true)
    {out : ProofBox} (run : prefixSum logCellCount=some out) :
    (∑ i ∈ Finset.range logCellCount,realTerm i) ≤ realWord out.hi := by
  have hr : block 0 logCellCount=some out :=
    (congrFun prefixSum_function_exact logCellCount).symm.trans run
  have hc : ∀ j < logCellCount, ∀ b, cell (0+j)=some b →
      RealBox.Contains 128 b (realTerm (0+j)) := by
    intro j hj b hb
    have hb' : cell j=some b := by simpa only [Nat.zero_add] using hb
    have hs := cell_real_sound (i:=j) hj (domains j hj) (b:=b) hb'
    simpa only [Nat.zero_add] using hs
  have hs := block_real_sum_upper 0 logCellCount realTerm hc (out:=out) hr
  simpa only [Nat.zero_add] using hs

theorem actual_weight_budget (domains : ∀ i < logCellCount, cellDomain i=true)
    {out : ProofBox} (run : prefixSum logCellCount=some out)
    (wordBound : realWord out.hi ≤ 8433850764/1000000000000) :
    finalCoefficient heightEndpoint fullC pointD logCellCount ≤ 8441646/1000000000 := by
  have hf := (actual_weight_sum_bound domains (out:=out) run).trans wordBound
  have ht := pairedFactor_upper_fraction (r:=(1/8:ℝ))
    (by norm_num : (0:ℝ) ≤ 160) (by norm_num : (160:ℝ) < 330)
  have hc := pairedFactor_upper_fraction (r:=(1/8:ℝ))
    (by norm_num : (0:ℝ) ≤ 880/3) (by norm_num : (880/3:ℝ) < 330)
  have hb := spectralBase_330_tiny
  unfold finalCoefficient profileCoefficient
  have sumForm : (∑ i ∈ Finset.range logCellCount,realTerm i)=
      2*(∑ i ∈ Finset.range logCellCount,
        ((1/heightEndpoint i-1/heightEndpoint (i+1))*fullC i)*
          pairedFactor (pointD i) (1/8) 330) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [realTerm,mul_assoc]
  rw [sumForm] at hf
  norm_num at ht hc
  nlinarith

theorem pi_008441646_from_actual_weights (source : SourcePointOutputFamily)
    (domains : ∀ i < logCellCount, cellDomain i=true)
    {out : ProofBox} (run : prefixSum logCellCount=some out)
    (wordBound : realWord out.hi ≤ 8433850764/1000000000000)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  have hcaps := source_actual_height_caps source domains h hRH
  have hb := source_pi_from_count_cells heightEndpoint_monotone heightEndpoint_zero
    heightEndpoint_last h hcaps hCHJ hrvm hsmall hlow hRH hQRH
  have budget := actual_weight_budget domains (out:=out) run wordBound
  intro x hx
  have hh := hb x hx
  have hx0 : 0 < x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right budget (by positivity))

#print axioms actual_weight_sum_bound
#print axioms actual_weight_budget
#print axioms pi_008441646_from_actual_weights
end SynergyHeightC.MainWeightModel
