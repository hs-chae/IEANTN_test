import RamPushCore
namespace RHOcticPush.Ram
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma c_low_0 : (106150293127/500000000000:ℝ) ≤ -88/100-shift5 (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ)+lowerNoMax (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_low_0 : 68/100+shift5 ((7116933/262144:ℝ)-1) ((238807312092525/8796093022208:ℝ)-1)+upperPowers ((7116933/262144:ℝ)-1) ≤ (1800461384081/1000000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_low_0 : (1/5000:ℝ) ≤ enhancedMargin (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ) (106150293127/500000000000:ℝ) (1800461384081/1000000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_low_0 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (7116933/262144:ℝ) ≤ z) (hu : z ≤ (238807312092525/8796093022208:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/5000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_low_0.trans (by
    linarith [lowerNoMax_le (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ)] :
      -88/100-shift5 (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ)+lowerNoMax (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ) ≤
      -88/100-shift5 (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ)+lowerPowers (7116933/262144:ℝ) (238807312092525/8796093022208:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (7116933/262144:ℝ)) (by norm_num : (238807312092525/8796093022208:ℝ) ≤ 42) hl hu hcut hcap hc d_low_0
  exact m_low_0.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (7116933/262144:ℝ)) hl hu
    (by norm_num : 0 ≤ (106150293127/500000000000:ℝ)) (by norm_num : 0 ≤ (1800461384081/1000000000000:ℝ)) hb.1 hb.2)

lemma c_low_1 : (53074752353/250000000000:ℝ) ≤ -88/100-shift5 (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ)+lowerNoMax (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_low_1 : 68/100+shift5 ((238807312092525/8796093022208:ℝ)-1) ((119404989893997/4398046511104:ℝ)-1)+upperPowers ((238807312092525/8796093022208:ℝ)-1) ≤ (45011461449/25000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_low_1 : (1/5000:ℝ) ≤ enhancedMargin (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ) (53074752353/250000000000:ℝ) (45011461449/25000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_low_1 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (238807312092525/8796093022208:ℝ) ≤ z) (hu : z ≤ (119404989893997/4398046511104:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/5000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_low_1.trans (by
    linarith [lowerNoMax_le (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ)] :
      -88/100-shift5 (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ)+lowerNoMax (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ) ≤
      -88/100-shift5 (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ)+lowerPowers (238807312092525/8796093022208:ℝ) (119404989893997/4398046511104:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (238807312092525/8796093022208:ℝ)) (by norm_num : (119404989893997/4398046511104:ℝ) ≤ 42) hl hu hcut hcap hc d_low_1
  exact m_low_1.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (238807312092525/8796093022208:ℝ)) hl hu
    (by norm_num : 0 ≤ (53074752353/250000000000:ℝ)) (by norm_num : 0 ≤ (45011461449/25000000000:ℝ)) hb.1 hb.2)

lemma c_low_2 : (42459091671/200000000000:ℝ) ≤ -88/100-shift5 (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ)+lowerNoMax (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_low_2 : 68/100+shift5 ((119404989893997/4398046511104:ℝ)-1) ((59703828794733/2199023255552:ℝ)-1)+upperPowers ((119404989893997/4398046511104:ℝ)-1) ≤ (1800455541871/1000000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_low_2 : (1/5000:ℝ) ≤ enhancedMargin (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ) (42459091671/200000000000:ℝ) (1800455541871/1000000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_low_2 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (119404989893997/4398046511104:ℝ) ≤ z) (hu : z ≤ (59703828794733/2199023255552:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/5000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_low_2.trans (by
    linarith [lowerNoMax_le (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ)] :
      -88/100-shift5 (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ)+lowerNoMax (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ) ≤
      -88/100-shift5 (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ)+lowerPowers (119404989893997/4398046511104:ℝ) (59703828794733/2199023255552:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (119404989893997/4398046511104:ℝ)) (by norm_num : (59703828794733/2199023255552:ℝ) ≤ 42) hl hu hcut hcap hc d_low_2
  exact m_low_2.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (119404989893997/4398046511104:ℝ)) hl hu
    (by norm_num : 0 ≤ (42459091671/200000000000:ℝ)) (by norm_num : 0 ≤ (1800455541871/1000000000000:ℝ)) hb.1 hb.2)

lemma c_low_3 : (212288357079/1000000000000:ℝ) ≤ -88/100-shift5 (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ)+lowerNoMax (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_low_3 : 68/100+shift5 ((59703828794733/2199023255552:ℝ)-1) ((29853248245101/1099511627776:ℝ)-1)+upperPowers ((59703828794733/2199023255552:ℝ)-1) ≤ (90022485509/50000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_low_3 : (1/5000:ℝ) ≤ enhancedMargin (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ) (212288357079/1000000000000:ℝ) (90022485509/50000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_low_3 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (59703828794733/2199023255552:ℝ) ≤ z) (hu : z ≤ (29853248245101/1099511627776:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/5000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_low_3.trans (by
    linarith [lowerNoMax_le (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ)] :
      -88/100-shift5 (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ)+lowerNoMax (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ) ≤
      -88/100-shift5 (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ)+lowerPowers (59703828794733/2199023255552:ℝ) (29853248245101/1099511627776:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (59703828794733/2199023255552:ℝ)) (by norm_num : (29853248245101/1099511627776:ℝ) ≤ 42) hl hu hcut hcap hc d_low_3
  exact m_low_3.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (59703828794733/2199023255552:ℝ)) hl hu
    (by norm_num : 0 ≤ (212288357079/1000000000000:ℝ)) (by norm_num : 0 ≤ (90022485509/50000000000:ℝ)) hb.1 hb.2)

theorem bridge_low (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (617500000000:ℝ) ≤ exp z)
    (hcap : exp z ≤ 619000000000) : (1/5000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (7116933/262144:ℝ) ≤ (617500000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (7116933/262144:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (29853248245101/1099511627776:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_619
    norm_num only [Real.log_exp] at h
    convert h using 1 <;> norm_num
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (238807312092525/8796093022208:ℝ)
  · exact gap_low_0 hRH hGM hP hJ hT hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (119404989893997/4398046511104:ℝ)
  · exact gap_low_1 hRH hGM hP hJ hT hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (59703828794733/2199023255552:ℝ)
  · exact gap_low_2 hRH hGM hP hJ hT hL hU (by linarith) h2 hc hp
  exact gap_low_3 hRH hGM hP hJ hT hL hU
    (by linarith) hu hc hp

#print axioms bridge_low
end RHOcticPush.Ram
