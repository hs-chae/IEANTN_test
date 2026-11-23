import Ram620Finite
import ActualSourceResult
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma c_number_0 : (53004300831/250000000000:ℝ) ≤ -88/100-shift (444873/16384:ℝ) (55611/2048:ℝ)+lowerNoMax (444873/16384:ℝ) (55611/2048:ℝ) := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_0 : 68/100+shift ((444873/16384:ℝ)-1) ((55611/2048:ℝ)-1)+upperPowers ((444873/16384:ℝ)-1) ≤ (1800689854063/1000000000000:ℝ) := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_0 : (1/1000:ℝ) ≤ enhancedMargin (444873/16384:ℝ) (55611/2048:ℝ) (53004300831/250000000000:ℝ) (1800689854063/1000000000000:ℝ) := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_0 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (444873/16384:ℝ) ≤ z) (hu : z ≤ (55611/2048:ℝ))
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_0.trans (by
    linarith [lowerNoMax_le (444873/16384:ℝ) (55611/2048:ℝ)] :
      -88/100-shift (444873/16384:ℝ) (55611/2048:ℝ)+lowerNoMax (444873/16384:ℝ) (55611/2048:ℝ) ≤ -88/100-shift (444873/16384:ℝ) (55611/2048:ℝ)+lowerPowers (444873/16384:ℝ) (55611/2048:ℝ))
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (444873/16384:ℝ)) (by norm_num : (55611/2048:ℝ) ≤ 42) hl hu hcut hcap hc d_number_0
  exact margin_0.trans (enhanced_slab (by norm_num : 27 ≤ (444873/16384:ℝ)) hl hu
    (by norm_num : 0 ≤ (53004300831/250000000000:ℝ)) (by norm_num : 0 ≤ (1800689854063/1000000000000:ℝ)) hb.1 hb.2)

lemma c_number_1 : (211994593681/1000000000000:ℝ) ≤ -88/100-shift (55611/2048:ℝ) (111237/4096:ℝ)+lowerNoMax (55611/2048:ℝ) (111237/4096:ℝ) := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_1 : 68/100+shift ((55611/2048:ℝ)-1) ((111237/4096:ℝ)-1)+upperPowers ((55611/2048:ℝ)-1) ≤ (1800681106803/1000000000000:ℝ) := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_1 : (1/1000:ℝ) ≤ enhancedMargin (55611/2048:ℝ) (111237/4096:ℝ) (211994593681/1000000000000:ℝ) (1800681106803/1000000000000:ℝ) := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_1 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (55611/2048:ℝ) ≤ z) (hu : z ≤ (111237/4096:ℝ))
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_1.trans (by
    linarith [lowerNoMax_le (55611/2048:ℝ) (111237/4096:ℝ)] :
      -88/100-shift (55611/2048:ℝ) (111237/4096:ℝ)+lowerNoMax (55611/2048:ℝ) (111237/4096:ℝ) ≤ -88/100-shift (55611/2048:ℝ) (111237/4096:ℝ)+lowerPowers (55611/2048:ℝ) (111237/4096:ℝ))
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (55611/2048:ℝ)) (by norm_num : (111237/4096:ℝ) ≤ 42) hl hu hcut hcap hc d_number_1
  exact margin_1.trans (enhanced_slab (by norm_num : 27 ≤ (55611/2048:ℝ)) hl hu
    (by norm_num : 0 ≤ (211994593681/1000000000000:ℝ)) (by norm_num : 0 ≤ (1800681106803/1000000000000:ℝ)) hb.1 hb.2)

lemma c_number_2 : (211975613207/1000000000000:ℝ) ≤ -88/100-shift (111237/4096:ℝ) (27813/1024:ℝ)+lowerNoMax (111237/4096:ℝ) (27813/1024:ℝ) := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_2 : 68/100+shift ((111237/4096:ℝ)-1) ((27813/1024:ℝ)-1)+upperPowers ((111237/4096:ℝ)-1) ≤ (450161450133/250000000000:ℝ) := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_2 : (1/1000:ℝ) ≤ enhancedMargin (111237/4096:ℝ) (27813/1024:ℝ) (211975613207/1000000000000:ℝ) (450161450133/250000000000:ℝ) := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_2 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (111237/4096:ℝ) ≤ z) (hu : z ≤ (27813/1024:ℝ))
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_2.trans (by
    linarith [lowerNoMax_le (111237/4096:ℝ) (27813/1024:ℝ)] :
      -88/100-shift (111237/4096:ℝ) (27813/1024:ℝ)+lowerNoMax (111237/4096:ℝ) (27813/1024:ℝ) ≤ -88/100-shift (111237/4096:ℝ) (27813/1024:ℝ)+lowerPowers (111237/4096:ℝ) (27813/1024:ℝ))
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (111237/4096:ℝ)) (by norm_num : (27813/1024:ℝ) ≤ 42) hl hu hcut hcap hc d_number_2
  exact margin_2.trans (enhanced_slab (by norm_num : 27 ≤ (111237/4096:ℝ)) hl hu
    (by norm_num : 0 ≤ (211975613207/1000000000000:ℝ)) (by norm_num : 0 ≤ (450161450133/250000000000:ℝ)) hb.1 hb.2)

lemma c_number_3 : (105942663223/500000000000:ℝ) ≤ -88/100-shift (27813/1024:ℝ) (6957/256:ℝ)+lowerNoMax (27813/1024:ℝ) (6957/256:ℝ) := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_3 : 68/100+shift ((27813/1024:ℝ)-1) ((6957/256:ℝ)-1)+upperPowers ((27813/1024:ℝ)-1) ≤ (900305424507/500000000000:ℝ) := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_3 : (1/1000:ℝ) ≤ enhancedMargin (27813/1024:ℝ) (6957/256:ℝ) (105942663223/500000000000:ℝ) (900305424507/500000000000:ℝ) := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_3 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (27813/1024:ℝ) ≤ z) (hu : z ≤ (6957/256:ℝ))
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_3.trans (by
    linarith [lowerNoMax_le (27813/1024:ℝ) (6957/256:ℝ)] :
      -88/100-shift (27813/1024:ℝ) (6957/256:ℝ)+lowerNoMax (27813/1024:ℝ) (6957/256:ℝ) ≤ -88/100-shift (27813/1024:ℝ) (6957/256:ℝ)+lowerPowers (27813/1024:ℝ) (6957/256:ℝ))
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (27813/1024:ℝ)) (by norm_num : (6957/256:ℝ) ≤ 42) hl hu hcut hcap hc d_number_3
  exact margin_3.trans (enhanced_slab (by norm_num : 27 ≤ (27813/1024:ℝ)) hl hu
    (by norm_num : 0 ≤ (105942663223/500000000000:ℝ)) (by norm_num : 0 ≤ (900305424507/500000000000:ℝ)) hb.1 hb.2)

lemma c_number_4 : (52881487017/250000000000:ℝ) ≤ -88/100-shift (6957/256:ℝ) (1743/64:ℝ)+lowerNoMax (6957/256:ℝ) (1743/64:ℝ) := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_4 : 68/100+shift ((6957/256:ℝ)-1) ((1743/64:ℝ)-1)+upperPowers ((6957/256:ℝ)-1) ≤ (45011781741/25000000000:ℝ) := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_4 : (1/1000:ℝ) ≤ enhancedMargin (6957/256:ℝ) (1743/64:ℝ) (52881487017/250000000000:ℝ) (45011781741/25000000000:ℝ) := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_4 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ))
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_4.trans (by
    linarith [lowerNoMax_le (6957/256:ℝ) (1743/64:ℝ)] :
      -88/100-shift (6957/256:ℝ) (1743/64:ℝ)+lowerNoMax (6957/256:ℝ) (1743/64:ℝ) ≤ -88/100-shift (6957/256:ℝ) (1743/64:ℝ)+lowerPowers (6957/256:ℝ) (1743/64:ℝ))
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (6957/256:ℝ)) (by norm_num : (1743/64:ℝ) ≤ 42) hl hu hcut hcap hc d_number_4
  exact margin_4.trans (enhanced_slab (by norm_num : 27 ≤ (6957/256:ℝ)) hl hu
    (by norm_num : 0 ≤ (52881487017/250000000000:ℝ)) (by norm_num : 0 ≤ (45011781741/25000000000:ℝ)) hb.1 hb.2)

theorem finite_bridge (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (444873/16384:ℝ) ≤ (620000000000:ℝ) := by interval_decide 80 (trust := kernel)
  have hhi : (640000000000:ℝ) ≤ exp (1743/64:ℝ) := by interval_decide 80 (trust := kernel)
  have hl : (444873/16384:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1743/64:ℝ) := exp_le_exp.mp (hcap.trans hhi)
  by_cases h0 : z ≤ (55611/2048:ℝ)
  · exact gap_0 hRH hGM hP hJ hT hL hU (by linarith) h0 hcut hcap
  by_cases h1 : z ≤ (111237/4096:ℝ)
  · exact gap_1 hRH hGM hP hJ hT hL hU (by linarith) h1 hcut hcap
  by_cases h2 : z ≤ (27813/1024:ℝ)
  · exact gap_2 hRH hGM hP hJ hT hL hU (by linarith) h2 hcut hcap
  by_cases h3 : z ≤ (6957/256:ℝ)
  · exact gap_3 hRH hGM hP hJ hT hL hU (by linarith) h3 hcut hcap
  exact gap_4 hRH hGM hP hJ hT hL hU (by linarith) hu hcut hcap

theorem actual_ramanujan_620b (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (620000000000:ℝ) ≤ x) : (1/1000:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases h640 : (640000000000:ℝ) ≤ x
  · have h := source_ramanujan_640b hRH hT2 hJ hL hU hS h640
    linarith
  · have h := finite_bridge hRH hGM hP hJ hT1 hL hU (z:=log x)
      (by simpa only [exp_log hx0] using hx)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h
#print axioms finite_bridge
#print axioms actual_ramanujan_620b
#check @actual_ramanujan_620b
end RHLimit.Ram620
