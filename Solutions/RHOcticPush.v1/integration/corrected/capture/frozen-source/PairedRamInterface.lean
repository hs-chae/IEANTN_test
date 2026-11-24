import Corr610Result
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

/-- The same signed arithmetic observable as the public paired-transfer node.
It is proved by GM.actual_pair_upper from old source inputs, not a prime-count
success assumption. Keeping it explicit permits real typed network reuse. -/
def PairTransfer : Prop := ∀ K y x : ℝ, 0 ≤ K → K ≤ exp 1 → exp 15 ≤ y → y ≤ x →
  K*GM.error x-exp 1*GM.error y ≤ GM.pairBudget K y x

theorem actual_margin_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {l u z k a b : ℝ} (hl : 27 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u)
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000)
    (hk0 : 0 ≤ k) (hke : k ≤ exp 1) (hkw : k ≤ 2*pN 20 u)
    (ha : a ≤ -88/100+lowerPowers l u)
    (hb : 68/100+upperPowers (l-1) ≤ b) : margin k a b z ≤ RamStudy.RG (exp z) := by
  have hz27 : (27:ℝ) ≤ z := hl.trans hlz
  have hz0 : 0 < z := by linarith
  have hzm1 : 0 < z-1 := by linarith
  have hz42 : z ≤ 42 := hzu.trans hu
  have hz2 : 2 ≤ exp z := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hc0 := (source_deficit_pos hU hz0 hz2 hz42).le
  have hcq := source_deficit_upper hL hz0 hz2 hz42
  have hsq := pow_le_pow_left₀ hc0 hcq 2
  have hF : 0 ≤ F z := by unfold F; positivity
  have hH : 0 ≤ H z := by unfold H; positivity
  have hQ : 0 ≤ Q z := by unfold Q; positivity
  have hT : 0 ≤ T z := by unfold T; positivity
  have hbase := SharpBase.actual_sharp_base hz27
  have hactual := actual_signed_gap (by linarith : 1 < z) hbase
    (le_refl (deficit z)) (le_refl (deficit (z-1)))
  have hactual' : SharpBase.sharpBase z-H z*deficit (z-1)+
      2*RamStudy.w z*F z*deficit z-(deficit z)^2*Q z ≤ RamStudy.RG (exp z) := by
    convert hactual using 1 <;> unfold F H Q <;> ring
  have hw : pN 20 u ≤ RamStudy.w z :=
    (pN_antitone hz0 hzu 20).trans (by
      simpa only [actual_w_eq] using (actual_factorial_barrier26 (by linarith : 26 ≤ z)).1)
  have hkactual : k ≤ 2*RamStudy.w z := by linarith
  have hkwc := mul_le_mul_of_nonneg_right hkactual (mul_nonneg hF hc0)
  have hsqQ := mul_le_mul_of_nonneg_right hsq hQ
  have ht := table1_bridge480 hTab hcut hcap
  have hpow := powers_lower hL (by linarith : 26 ≤ l) hlz hzu hu
  have hpow' := powers_upper hU (by linarith : 26 ≤ l-1)
    (by linarith : l-1 ≤ z-1) (by linarith : z-1 ≤ 42)
  have ha' : a ≤ psiDeficit z+primePart z := by linarith
  have hb' : psiDeficit (z-1)+primePart (z-1) ≤ b := by linarith
  have hpa := mul_le_mul_of_nonneg_left ha' (mul_nonneg hk0 hF)
  have hpb := mul_le_mul_of_nonneg_left hb' hH
  have hpair := paired k (exp (z-1)) (exp z) hk0 hke
    (exp_le_exp.mpr (by linarith)) (exp_le_exp.mpr (by linarith))
  have hpt := mul_le_mul_of_nonneg_left hpair hT
  have hidentity := linear_identity (k := k) hz0.ne' (by linarith : z ≠ 1)
  unfold margin
  nlinarith only [hactual',hkwc,hsqQ,hpa,hpb,hpt,hidentity]

theorem gap610_0_of_pair (paired : PairTransfer)
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
  have h := actual_margin_of_pair paired hTab hL hU
    (by norm_num : 27 ≤ (6947/256:ℝ)) (by norm_num : (14228417/524288:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_0
  have hn := numeric610_0 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h


theorem gap610_1_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (14228417/524288:ℝ) ≤ z) (hu : z ≤ (7114689/262144:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (103989/50000:ℝ) ≤ 2*pN 20 (7114689/262144:ℝ) := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower610_1.trans (by
    linarith [lowerNoMax_le (14228417/524288:ℝ) (7114689/262144:ℝ)] :
      -88/100+lowerNoMax (14228417/524288:ℝ) (7114689/262144:ℝ) ≤ -88/100+lowerPowers (14228417/524288:ℝ) (7114689/262144:ℝ))
  have h := actual_margin_of_pair paired hTab hL hU
    (by norm_num : 27 ≤ (14228417/524288:ℝ)) (by norm_num : (7114689/262144:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_1
  have hn := numeric610_1 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h


theorem gap610_2_of_pair (paired : PairTransfer)
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
  have h := actual_margin_of_pair paired hTab hL hU
    (by norm_num : 27 ≤ (7114689/262144:ℝ)) (by norm_num : (3557825/131072:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_2
  have hn := numeric610_2 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h


theorem gap610_3_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (3557825/131072:ℝ) ≤ z) (hu : z ≤ (1779393/65536:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : (103989/50000:ℝ) ≤ 2*pN 20 (1779393/65536:ℝ) := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower610_3.trans (by
    linarith [lowerNoMax_le (3557825/131072:ℝ) (1779393/65536:ℝ)] :
      -88/100+lowerNoMax (3557825/131072:ℝ) (1779393/65536:ℝ) ≤ -88/100+lowerPowers (3557825/131072:ℝ) (1779393/65536:ℝ))
  have h := actual_margin_of_pair paired hTab hL hU
    (by norm_num : 27 ≤ (3557825/131072:ℝ)) (by norm_num : (1779393/65536:ℝ) ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ (103989/50000:ℝ))
    (by interval_decide 40 (trust := kernel) : (103989/50000:ℝ) ≤ exp 1) hk ha upper610_3
  have hn := numeric610_3 z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h


theorem bridge610_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (610000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 619000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (6947/256:ℝ) ≤ (610000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (6947/256:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1779393/65536:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_619
    norm_num only [Real.log_exp] at h
    norm_num at h ⊢
    linarith
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (14228417/524288:ℝ)
  · exact gap610_0_of_pair paired hTab hL hU hl h0 hc hp
  by_cases h1 : z ≤ (7114689/262144:ℝ)
  · exact gap610_1_of_pair paired hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (3557825/131072:ℝ)
  · exact gap610_2_of_pair paired hTab hL hU (by linarith) h2 hc hp
  exact gap610_3_of_pair paired hTab hL hU (by linarith) hu hc hp

theorem actual_ramanujan_610b_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (610000000000:ℝ) ≤ x) : (1/1000:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases h620 : (620000000000:ℝ) ≤ x
  · exact RHLimit.Ram620.actual_ramanujan_620b hRH hGM hP hJ hT1 hT2 hL hU hS h620
  by_cases h619 : (619000000000:ℝ) ≤ x
  · have h := RHOcticPush.Ram.bridge_mid hRH hGM hP hJ hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h619)
      (by rw [exp_log hx0]; linarith)
    rw [exp_log hx0] at h
    linarith
  have h := bridge610_of_pair paired hT1 hL hU (z := log x)
    (by simpa only [exp_log hx0] using hx)
    (by rw [exp_log hx0]; linarith)
  simpa only [exp_log hx0] using h


#print axioms actual_margin_of_pair
#print axioms bridge610_of_pair
#print axioms actual_ramanujan_610b_of_pair
end RHOcticPush.Correlated
