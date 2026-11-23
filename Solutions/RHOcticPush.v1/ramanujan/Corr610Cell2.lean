import CorrelatedNumeric
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

lemma lower610_2 : (43824261827/200000000000:ℝ) ≤ -88/100+lowerNoMax (7114689/262144:ℝ) (3557825/131072:ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper610_2 : 68/100+upperPowers ((7114689/262144:ℝ)-1) ≤ (1793133558609/1000000000000:ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

/-- Certified for EVERY real parameter in this closed interval. -/
lemma numeric610_2 : ∀ z ∈ Set.Icc (7114689/262144:ℝ) (3557825/131072:ℝ),
    (1/1000:ℝ) ≤ numericMargin (103989/50000:ℝ) (43824261827/200000000000:ℝ) (1793133558609/1000000000000:ℝ) z := by
  unfold numericMargin F H Q T numericBudget q
  simp_rw [fullBase_explicit]
  certify_bound 40 (trust := kernel)

theorem gap610_2 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (7114689/262144:ℝ) ≤ z) (hu : z ≤ (3557825/131072:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (103989/50000:ℝ) ≤ 2*pN 20 (3557825/131072:ℝ) := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower610_2.trans (by
    linarith [lowerNoMax_le (7114689/262144:ℝ) (3557825/131072:ℝ)] :
      -88/100+lowerNoMax (7114689/262144:ℝ) (3557825/131072:ℝ) ≤ -88/100+lowerPowers (7114689/262144:ℝ) (3557825/131072:ℝ))
  have h := actual_margin hRH hGM hP hJ hTab hL hU
    (by norm_num : 27 ≤ (7114689/262144:ℝ)) (by norm_num : (3557825/131072:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_2
  have hn := numeric610_2 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric610_2
#print axioms gap610_2
end RHOcticPush.Correlated
