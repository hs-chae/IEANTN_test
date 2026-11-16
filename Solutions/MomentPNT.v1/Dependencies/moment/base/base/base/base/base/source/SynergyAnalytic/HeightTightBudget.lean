import SynergyAnalytic.HeightFiniteBudget
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kernel_budget_word_total_tight :
    (∑b∈Finset.range 24,blockWords[b]?.getD 0)*1000000000000 ≤ 8433850764*scale p := by decide +kernel

theorem budget_term_total_tight :
    (∑i∈Finset.range logCellCount,budgetTerm i) ≤ 8433850764/1000000000000 := by
  have hs : (∑b∈Finset.range 24,∑j∈Finset.range 32,budgetTerm (32*b+j)) ≤
      ∑b∈Finset.range 24,(blockWords[b]?.getD 0:ℝ)/(scale p:ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    exact budget_block_upper (Finset.mem_range.mp hb)
      ((List.all_eq_true.mp kernel_budget_blocks) b (List.mem_range.mpr (Finset.mem_range.mp hb)))
  have hcast : ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)*1000000000000 ≤ 8433850764*(scale p:ℝ) := by
    exact_mod_cast kernel_budget_word_total_tight
  have hn : ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)/(scale p:ℝ) ≤ 8433850764/1000000000000 := by
    apply (div_le_iff₀ (RealBox.scale_real_pos p)).mpr
    linarith
  have hs' : (∑i∈Finset.range logCellCount,budgetTerm i) ≤
      ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)/(scale p:ℝ) := by
    rw [show logCellCount=32*24 by rfl,sum_blocks]
    convert hs using 1
    rw [Finset.sum_div]
  exact hs'.trans hn

theorem finite_height_budget_tight :
    2*(∑i∈Finset.range logCellCount,((1/heightEndpoint i-1/heightEndpoint (i+1))*cValue i)*
      pairedFactor (DValue i) (1/8) 330) ≤ 8433850764/1000000000000 := by
  rw [Finset.mul_sum]
  simpa only [budgetTerm,mul_assoc] using budget_term_total_tight

theorem final_height_budget_tight :
    finalCoefficient heightEndpoint cValue DValue logCellCount ≤ 8441646/1000000000 := by
  have ht := pairedFactor_upper_fraction (r:=(1/8:ℝ)) (by norm_num : (0:ℝ)≤160) (by norm_num : (160:ℝ)<330)
  have hc := pairedFactor_upper_fraction (r:=(1/8:ℝ)) (by norm_num : (0:ℝ)≤880/3) (by norm_num : (880/3:ℝ)<330)
  have hb := spectralBase_330_tiny
  have hf := finite_height_budget_tight
  unfold finalCoefficient profileCoefficient
  norm_num at ht hc
  nlinarith

#print axioms kernel_budget_word_total_tight
#print axioms finite_height_budget_tight
#print axioms final_height_budget_tight
end SynergyAnalytic.HeightPoint
