import CorrelatedNumeric
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

lemma lower610_0 : (219154240797/1000000000000:ℝ) ≤ -88/100+lowerNoMax (6947/256:ℝ) (14228417/524288:ℝ) := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper610_0 : 68/100+upperPowers ((6947/256:ℝ)-1) ≤ (1793166413231/1000000000000:ℝ) := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

/-- Certified for EVERY real parameter in this closed interval. -/
lemma numeric610_0 : ∀ z ∈ Set.Icc (6947/256:ℝ) (14228417/524288:ℝ),
    (1/1000:ℝ) ≤ numericMargin (103989/50000:ℝ) (219154240797/1000000000000:ℝ) (1793166413231/1000000000000:ℝ) z := by
  unfold numericMargin F H Q T numericBudget q
  simp_rw [fullBase_explicit]
  certify_bound 40 (trust := kernel)

theorem gap610_0 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6947/256:ℝ) ≤ z) (hu : z ≤ (14228417/524288:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (103989/50000:ℝ) ≤ 2*pN 20 (14228417/524288:ℝ) := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower610_0.trans (by
    linarith [lowerNoMax_le (6947/256:ℝ) (14228417/524288:ℝ)] :
      -88/100+lowerNoMax (6947/256:ℝ) (14228417/524288:ℝ) ≤ -88/100+lowerPowers (6947/256:ℝ) (14228417/524288:ℝ))
  have h := actual_margin hRH hGM hP hJ hTab hL hU
    (by norm_num : 27 ≤ (6947/256:ℝ)) (by norm_num : (14228417/524288:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_0
  have hn := numeric610_0 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric610_0
#print axioms gap610_0
end RHOcticPush.Correlated
