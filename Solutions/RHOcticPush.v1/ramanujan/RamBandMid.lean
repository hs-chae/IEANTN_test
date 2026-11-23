import RamPushCore
namespace RHOcticPush.Ram
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma c_mid_0 : (212284694119/1000000000000:ℝ) ≤ -88/100-shift5 (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ)+lowerNoMax (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_mid_0 : 68/100+shift5 ((7117569/262144:ℝ)-1) ((29854135604817/1099511627776:ℝ)-1)+upperPowers ((7117569/262144:ℝ)-1) ≤ (360087599431/200000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_mid_0 : (3/2000:ℝ) ≤ enhancedMargin (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ) (212284694119/1000000000000:ℝ) (360087599431/200000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_mid_0 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (7117569/262144:ℝ) ≤ z) (hu : z ≤ (29854135604817/1099511627776:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (3/2000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_mid_0.trans (by
    linarith [lowerNoMax_le (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ)] :
      -88/100-shift5 (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ)+lowerNoMax (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ) ≤
      -88/100-shift5 (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ)+lowerPowers (7117569/262144:ℝ) (29854135604817/1099511627776:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (7117569/262144:ℝ)) (by norm_num : (29854135604817/1099511627776:ℝ) ≤ 42) hl hu hcut hcap hc d_mid_0
  exact m_mid_0.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (7117569/262144:ℝ)) hl hu
    (by norm_num : 0 ≤ (212284694119/1000000000000:ℝ)) (by norm_num : 0 ≤ (360087599431/200000000000:ℝ)) hb.1 hb.2)

lemma c_mid_1 : (212280498913/1000000000000:ℝ) ≤ -88/100-shift5 (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ)+lowerNoMax (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_mid_1 : 68/100+shift5 ((29854135604817/1099511627776:ℝ)-1) ((14927511541329/549755813888:ℝ)-1)+upperPowers ((29854135604817/1099511627776:ℝ)-1) ≤ (1800430213433/1000000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_mid_1 : (3/2000:ℝ) ≤ enhancedMargin (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ) (212280498913/1000000000000:ℝ) (1800430213433/1000000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_mid_1 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (29854135604817/1099511627776:ℝ) ≤ z) (hu : z ≤ (14927511541329/549755813888:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (3/2000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_mid_1.trans (by
    linarith [lowerNoMax_le (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ)] :
      -88/100-shift5 (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ)+lowerNoMax (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ) ≤
      -88/100-shift5 (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ)+lowerPowers (29854135604817/1099511627776:ℝ) (14927511541329/549755813888:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (29854135604817/1099511627776:ℝ)) (by norm_num : (14927511541329/549755813888:ℝ) ≤ 42) hl hu hcut hcap hc d_mid_1
  exact m_mid_1.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (29854135604817/1099511627776:ℝ)) hl hu
    (by norm_num : 0 ≤ (212280498913/1000000000000:ℝ)) (by norm_num : 0 ≤ (1800430213433/1000000000000:ℝ)) hb.1 hb.2)

theorem bridge_mid (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (619000000000:ℝ) ≤ exp z)
    (hcap : exp z ≤ 620000000000) : (3/2000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (7117569/262144:ℝ) ≤ (619000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (7117569/262144:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (14927511541329/549755813888:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_620
    norm_num only [Real.log_exp] at h
    convert h using 1 <;> norm_num
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (29854135604817/1099511627776:ℝ)
  · exact gap_mid_0 hRH hGM hP hJ hT hL hU (by linarith) h0 hc hp
  exact gap_mid_1 hRH hGM hP hJ hT hL hU
    (by linarith) hu hc hp

#print axioms bridge_mid
end RHOcticPush.Ram
