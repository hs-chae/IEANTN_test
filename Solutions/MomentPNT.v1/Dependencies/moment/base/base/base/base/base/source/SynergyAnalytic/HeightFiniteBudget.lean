import SynergyAnalytic.HeightBudgetChecks
import SynergyAnalytic.HeightBudgetTransfer
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sum_blocks (f:Nat→ℝ) (b:Nat) :
    (∑i∈Finset.range (32*b),f i)=∑j∈Finset.range b,∑k∈Finset.range 32,f (32*j+k) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ (fun j=>∑k∈Finset.range 32,f (32*j+k)) b]
    rw [Nat.mul_succ,Finset.sum_range_add,ih]

theorem budget_term_total :
    (∑i∈Finset.range logCellCount,budgetTerm i) ≤ 4217/500000 := by
  have hs : (∑b∈Finset.range 24,∑j∈Finset.range 32,budgetTerm (32*b+j)) ≤
      ∑b∈Finset.range 24,(blockWords[b]?.getD 0:ℝ)/(scale p:ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    exact budget_block_upper (Finset.mem_range.mp hb)
      ((List.all_eq_true.mp kernel_budget_blocks) b (List.mem_range.mpr (Finset.mem_range.mp hb)))
  have hcast : ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)*500000 ≤ 4217*(scale p:ℝ) := by
    exact_mod_cast kernel_budget_word_total
  have hn : ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)/(scale p:ℝ) ≤ 4217/500000 := by
    apply (div_le_iff₀ (RealBox.scale_real_pos p)).mpr
    linarith
  have hs' : (∑i∈Finset.range logCellCount,budgetTerm i) ≤
      ((∑b∈Finset.range 24,blockWords[b]?.getD 0):ℝ)/(scale p:ℝ) := by
    rw [show logCellCount=32*24 by rfl,sum_blocks]
    convert hs using 1
    push_cast
    rw [Finset.sum_div]
  exact hs'.trans hn

theorem finite_height_budget :
    2*(∑i∈Finset.range logCellCount,((1/heightEndpoint i-1/heightEndpoint (i+1))*cValue i)*
      pairedFactor (DValue i) (1/8) 330) ≤ 4217/500000 := by
  rw [Finset.mul_sum]
  simpa only [budgetTerm,mul_assoc] using budget_term_total

theorem final_height_budget :
    finalCoefficient heightEndpoint cValue DValue logCellCount ≤ 4221/500000 :=
  height_budget_of_finite_sum finite_height_budget

#print axioms finite_height_budget
#print axioms final_height_budget
end SynergyAnalytic.HeightPoint
