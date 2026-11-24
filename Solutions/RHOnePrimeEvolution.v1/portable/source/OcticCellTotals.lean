import OcticCellData
namespace RHOcticPush.Moments.Endpoint
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

lemma total0 : (∑ i ∈ Finset.range 7300, cap0Numerators.get i) ≤ 5703000000000 := by
  decide +kernel
lemma total1 : (∑ i ∈ Finset.Ico 100 7300, cap1Numerators.get i) ≤ 6170000000000 := by
  decide +kernel

lemma sum_cap0 : (∑ i ∈ Finset.range 7300, (cap0 i:ℝ)) ≤ (5703/1000:ℝ) := by
  unfold cap0
  push_cast
  rw [← Finset.sum_div]
  have h : ((∑ i ∈ Finset.range 7300, cap0Numerators.get i):ℝ) ≤ 5703000000000 := by
    exact_mod_cast total0
  have he : (∑ i ∈ Finset.range 7300, (cap0Numerators.get i:ℝ))=
      ((∑ i ∈ Finset.range 7300, cap0Numerators.get i):ℝ) := by push_cast; rfl
  rw [he]
  exact (div_le_div_of_nonneg_right h (by norm_num)).trans (by norm_num)

lemma sum_cap1 : (∑ i ∈ Finset.Ico 100 7300, (cap1 i:ℝ)) ≤ (617/100:ℝ) := by
  unfold cap1
  push_cast
  rw [← Finset.sum_div]
  have h : ((∑ i ∈ Finset.Ico 100 7300, cap1Numerators.get i):ℝ) ≤ 6170000000000 := by
    exact_mod_cast total1
  have he : (∑ i ∈ Finset.Ico 100 7300, (cap1Numerators.get i:ℝ))=
      ((∑ i ∈ Finset.Ico 100 7300, cap1Numerators.get i):ℝ) := by push_cast; rfl
  rw [he]
  exact (div_le_div_of_nonneg_right h (by norm_num)).trans (by norm_num)

#print axioms total0
#print axioms total1
#print axioms sum_cap0
#print axioms sum_cap1
end RHOcticPush.Moments.Endpoint
