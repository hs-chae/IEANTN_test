import PairedRamInterface
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

lemma lower607_3 : (219190659957/1000000000000:ℝ) ≤ -88/100+lowerNoMax (7112517/262144:ℝ) (3556299/131072:ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper607_3 : 68/100+upperPowers ((7112517/262144:ℝ)-1) ≤ (1793207845299/1000000000000:ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

/-- Certified for EVERY real parameter in this closed interval. -/
lemma numeric607_3 : ∀ z ∈ Set.Icc (7112517/262144:ℝ) (3556299/131072:ℝ),
    (1/10000:ℝ) ≤ numericMargin (5199/2500:ℝ) (219190659957/1000000000000:ℝ) (1793207845299/1000000000000:ℝ) z := by
  unfold numericMargin F H Q T numericBudget q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap607_3_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (7112517/262144:ℝ) ≤ z) (hu : z ≤ (3556299/131072:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/10000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (5199/2500:ℝ) ≤ 2*pN 20 (3556299/131072:ℝ) := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower607_3.trans (by
    linarith [lowerNoMax_le (7112517/262144:ℝ) (3556299/131072:ℝ)] :
      -88/100+lowerNoMax (7112517/262144:ℝ) (3556299/131072:ℝ) ≤ -88/100+lowerPowers (7112517/262144:ℝ) (3556299/131072:ℝ))
  have h := actual_margin_of_pair paired hTab hL hU
    (by norm_num : 27 ≤ (7112517/262144:ℝ)) (by norm_num : (3556299/131072:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (5199/2500:ℝ))
    (by interval_decide 40 (trust := kernel) : (5199/2500:ℝ) ≤ exp 1) hk ha upper607_3
  have hn := numeric607_3 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric607_3
#print axioms gap607_3_of_pair
end RHOcticPush.Correlated
