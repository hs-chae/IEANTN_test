import RamPushCore
namespace RHOcticPush.Ram
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
set_option Elab.async false

lemma c_high_0 : (212275103887/1000000000000:ℝ) ≤ -88/100-shift5 (889749/32768:ℝ) (477697811495115/17592186044416:ℝ)+lowerNoMax (889749/32768:ℝ) (477697811495115/17592186044416:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_0 : 68/100+shift5 ((889749/32768:ℝ)-1) ((477697811495115/17592186044416:ℝ)-1)+upperPowers ((889749/32768:ℝ)-1) ≤ (450105610899/250000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_0 : (1/400:ℝ) ≤ enhancedMargin (889749/32768:ℝ) (477697811495115/17592186044416:ℝ) (212275103887/1000000000000:ℝ) (450105610899/250000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_0 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (889749/32768:ℝ) ≤ z) (hu : z ≤ (477697811495115/17592186044416:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_0.trans (by
    linarith [lowerNoMax_le (889749/32768:ℝ) (477697811495115/17592186044416:ℝ)] :
      -88/100-shift5 (889749/32768:ℝ) (477697811495115/17592186044416:ℝ)+lowerNoMax (889749/32768:ℝ) (477697811495115/17592186044416:ℝ) ≤
      -88/100-shift5 (889749/32768:ℝ) (477697811495115/17592186044416:ℝ)+lowerPowers (889749/32768:ℝ) (477697811495115/17592186044416:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (889749/32768:ℝ)) (by norm_num : (477697811495115/17592186044416:ℝ) ≤ 42) hl hu hcut hcap hc d_high_0
  exact m_high_0.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (889749/32768:ℝ)) hl hu
    (by norm_num : 0 ≤ (212275103887/1000000000000:ℝ)) (by norm_num : 0 ≤ (450105610899/250000000000:ℝ)) hb.1 hb.2)

lemma c_high_1 : (53067487017/250000000000:ℝ) ≤ -88/100-shift5 (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ)+lowerNoMax (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_1 : 68/100+shift5 ((477697811495115/17592186044416:ℝ)-1) ((238857632954571/8796093022208:ℝ)-1)+upperPowers ((477697811495115/17592186044416:ℝ)-1) ≤ (450103219691/250000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_1 : (1/400:ℝ) ≤ enhancedMargin (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ) (53067487017/250000000000:ℝ) (450103219691/250000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_1 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (477697811495115/17592186044416:ℝ) ≤ z) (hu : z ≤ (238857632954571/8796093022208:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_1.trans (by
    linarith [lowerNoMax_le (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ)] :
      -88/100-shift5 (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ)+lowerNoMax (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ) ≤
      -88/100-shift5 (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ)+lowerPowers (477697811495115/17592186044416:ℝ) (238857632954571/8796093022208:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (477697811495115/17592186044416:ℝ)) (by norm_num : (238857632954571/8796093022208:ℝ) ≤ 42) hl hu hcut hcap hc d_high_1
  exact m_high_1.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (477697811495115/17592186044416:ℝ)) hl hu
    (by norm_num : 0 ≤ (53067487017/250000000000:ℝ)) (by norm_num : 0 ≤ (450103219691/250000000000:ℝ)) hb.1 hb.2)

lemma c_high_2 : (212258339493/1000000000000:ℝ) ≤ -88/100-shift5 (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ)+lowerNoMax (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_2 : 68/100+shift5 ((238857632954571/8796093022208:ℝ)-1) ((119437543684299/4398046511104:ℝ)-1)+upperPowers ((238857632954571/8796093022208:ℝ)-1) ≤ (900201673943/500000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_2 : (1/400:ℝ) ≤ enhancedMargin (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ) (212258339493/1000000000000:ℝ) (900201673943/500000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_2 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (238857632954571/8796093022208:ℝ) ≤ z) (hu : z ≤ (119437543684299/4398046511104:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_2.trans (by
    linarith [lowerNoMax_le (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ)] :
      -88/100-shift5 (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ)+lowerNoMax (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ) ≤
      -88/100-shift5 (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ)+lowerPowers (238857632954571/8796093022208:ℝ) (119437543684299/4398046511104:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (238857632954571/8796093022208:ℝ)) (by norm_num : (119437543684299/4398046511104:ℝ) ≤ 42) hl hu hcut hcap hc d_high_2
  exact m_high_2.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (238857632954571/8796093022208:ℝ)) hl hu
    (by norm_num : 0 ≤ (212258339493/1000000000000:ℝ)) (by norm_num : 0 ≤ (900201673943/500000000000:ℝ)) hb.1 hb.2)

lemma c_high_3 : (21223513133/100000000000:ℝ) ≤ -88/100-shift5 (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ)+lowerNoMax (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_3 : 68/100+shift5 ((119437543684299/4398046511104:ℝ)-1) ((59727499049163/2199023255552:ℝ)-1)+upperPowers ((119437543684299/4398046511104:ℝ)-1) ≤ (180038429133/100000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_3 : (1/400:ℝ) ≤ enhancedMargin (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ) (21223513133/100000000000:ℝ) (180038429133/100000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_3 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (119437543684299/4398046511104:ℝ) ≤ z) (hu : z ≤ (59727499049163/2199023255552:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_3.trans (by
    linarith [lowerNoMax_le (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ)] :
      -88/100-shift5 (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ)+lowerNoMax (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ) ≤
      -88/100-shift5 (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ)+lowerPowers (119437543684299/4398046511104:ℝ) (59727499049163/2199023255552:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (119437543684299/4398046511104:ℝ)) (by norm_num : (59727499049163/2199023255552:ℝ) ≤ 42) hl hu hcut hcap hc d_high_3
  exact m_high_3.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (119437543684299/4398046511104:ℝ)) hl hu
    (by norm_num : 0 ≤ (21223513133/100000000000:ℝ)) (by norm_num : 0 ≤ (180038429133/100000000000:ℝ)) hb.1 hb.2)

lemma c_high_4 : (212188750919/1000000000000:ℝ) ≤ -88/100-shift5 (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ)+lowerNoMax (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_4 : 68/100+shift5 ((59727499049163/2199023255552:ℝ)-1) ((29872476731595/1099511627776:ℝ)-1)+upperPowers ((59727499049163/2199023255552:ℝ)-1) ≤ (1800346199/1000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_4 : (1/400:ℝ) ≤ enhancedMargin (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ) (212188750919/1000000000000:ℝ) (1800346199/1000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_4 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (59727499049163/2199023255552:ℝ) ≤ z) (hu : z ≤ (29872476731595/1099511627776:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_4.trans (by
    linarith [lowerNoMax_le (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ)] :
      -88/100-shift5 (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ)+lowerNoMax (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ) ≤
      -88/100-shift5 (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ)+lowerPowers (59727499049163/2199023255552:ℝ) (29872476731595/1099511627776:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (59727499049163/2199023255552:ℝ)) (by norm_num : (29872476731595/1099511627776:ℝ) ≤ 42) hl hu hcut hcap hc d_high_4
  exact m_high_4.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (59727499049163/2199023255552:ℝ)) hl hu
    (by norm_num : 0 ≤ (212188750919/1000000000000:ℝ)) (by norm_num : 0 ≤ (1800346199/1000000000:ℝ)) hb.1 hb.2)

lemma c_high_5 : (42419226703/200000000000:ℝ) ≤ -88/100-shift5 (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ)+lowerNoMax (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ) := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_high_5 : 68/100+shift5 ((29872476731595/1099511627776:ℝ)-1) ((14944965572811/549755813888:ℝ)-1)+upperPowers ((29872476731595/1099511627776:ℝ)-1) ≤ (360054019473/200000000000:ℝ) := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_high_5 : (1/400:ℝ) ≤ enhancedMargin (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ) (42419226703/200000000000:ℝ) (360054019473/200000000000:ℝ)+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_high_5 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (29872476731595/1099511627776:ℝ) ≤ z) (hu : z ≤ (14944965572811/549755813888:ℝ))
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_high_5.trans (by
    linarith [lowerNoMax_le (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ)] :
      -88/100-shift5 (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ)+lowerNoMax (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ) ≤
      -88/100-shift5 (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ)+lowerPowers (29872476731595/1099511627776:ℝ) (14944965572811/549755813888:ℝ))
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ (29872476731595/1099511627776:ℝ)) (by norm_num : (14944965572811/549755813888:ℝ) ≤ 42) hl hu hcut hcap hc d_high_5
  exact m_high_5.trans (sharp_enhanced_slab (by norm_num : 27 ≤ (29872476731595/1099511627776:ℝ)) hl hu
    (by norm_num : 0 ≤ (42419226703/200000000000:ℝ)) (by norm_num : 0 ≤ (360054019473/200000000000:ℝ)) hb.1 hb.2)

theorem bridge_high (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (620000000000:ℝ) ≤ exp z)
    (hcap : exp z ≤ 640000000000) : (1/400:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (889749/32768:ℝ) ≤ (620000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (889749/32768:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (14944965572811/549755813888:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_640
    norm_num only [Real.log_exp] at h
    convert h using 1 <;> norm_num
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (477697811495115/17592186044416:ℝ)
  · exact gap_high_0 hRH hGM hP hJ hT hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (238857632954571/8796093022208:ℝ)
  · exact gap_high_1 hRH hGM hP hJ hT hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (119437543684299/4398046511104:ℝ)
  · exact gap_high_2 hRH hGM hP hJ hT hL hU (by linarith) h2 hc hp
  by_cases h3 : z ≤ (59727499049163/2199023255552:ℝ)
  · exact gap_high_3 hRH hGM hP hJ hT hL hU (by linarith) h3 hc hp
  by_cases h4 : z ≤ (29872476731595/1099511627776:ℝ)
  · exact gap_high_4 hRH hGM hP hJ hT hL hU (by linarith) h4 hc hp
  exact gap_high_5 hRH hGM hP hJ hT hL hU
    (by linarith) hu hc hp

#print axioms bridge_high
end RHOcticPush.Ram
