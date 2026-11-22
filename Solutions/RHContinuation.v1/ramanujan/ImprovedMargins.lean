import SeriesConsumer
namespace RHContinuation.Ramanujan
open Real IEANTN RamanujanPV.AnalyticTransition Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

theorem improved_scalar_0 : (1/20:ℝ) ≤ endpointMargin (6957/256:ℝ) (1743/64:ℝ) c0 d0 := by
  unfold endpointMargin c0 d0
  interval_decide 80 (trust := kernel)

theorem improved_leaf_0_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_0_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_0.trans (actual_slab_consumer (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ))
    (by norm_num) hl hu (proof_representation_0).1 (proof_representation_0).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_1 : (1/20:ℝ) ≤ endpointMargin (1743/64:ℝ) (879/32:ℝ) c1 d1 := by
  unfold endpointMargin c1 d1
  interval_decide 80 (trust := kernel)

theorem improved_leaf_1_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_1_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_1.trans (actual_slab_consumer (l:=(1743/64:ℝ)) (u:=(879/32:ℝ))
    (by norm_num) hl hu (proof_representation_1).1 (proof_representation_1).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_2 : (1/20:ℝ) ≤ endpointMargin (879/32:ℝ) (1773/64:ℝ) c2 d2 := by
  unfold endpointMargin c2 d2
  interval_decide 80 (trust := kernel)

theorem improved_leaf_2_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_2_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_2.trans (actual_slab_consumer (l:=(879/32:ℝ)) (u:=(1773/64:ℝ))
    (by norm_num) hl hu (proof_representation_2).1 (proof_representation_2).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_3 : (1/20:ℝ) ≤ endpointMargin (1773/64:ℝ) (447/16:ℝ) c3 d3 := by
  unfold endpointMargin c3 d3
  interval_decide 80 (trust := kernel)

theorem improved_leaf_3_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_3_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_3.trans (actual_slab_consumer (l:=(1773/64:ℝ)) (u:=(447/16:ℝ))
    (by norm_num) hl hu (proof_representation_3).1 (proof_representation_3).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_4 : (1/20:ℝ) ≤ endpointMargin (447/16:ℝ) (231/8:ℝ) c4 d4 := by
  unfold endpointMargin c4 d4
  interval_decide 80 (trust := kernel)

theorem improved_leaf_4_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_4_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_4.trans (actual_slab_consumer (l:=(447/16:ℝ)) (u:=(231/8:ℝ))
    (by norm_num) hl hu (proof_representation_4).1 (proof_representation_4).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_5 : (1/20:ℝ) ≤ endpointMargin (231/8:ℝ) (123/4:ℝ) c5 d5 := by
  unfold endpointMargin c5 d5
  interval_decide 80 (trust := kernel)

theorem improved_leaf_5_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_5_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_5.trans (actual_slab_consumer (l:=(231/8:ℝ)) (u:=(123/4:ℝ))
    (by norm_num) hl hu (proof_representation_5).1 (proof_representation_5).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_6 : (1/20:ℝ) ≤ endpointMargin (123/4:ℝ) (69/2:ℝ) c6 d6 := by
  unfold endpointMargin c6 d6
  interval_decide 80 (trust := kernel)

theorem improved_leaf_6_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_6_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_6.trans (actual_slab_consumer (l:=(123/4:ℝ)) (u:=(69/2:ℝ))
    (by norm_num) hl hu (proof_representation_6).1 (proof_representation_6).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_scalar_7 : (1/20:ℝ) ≤ endpointMargin (69/2:ℝ) (42:ℝ) c7 d7 := by
  unfold endpointMargin c7 d7
  interval_decide 80 (trust := kernel)

theorem improved_leaf_7_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_7_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact improved_scalar_7.trans (actual_slab_consumer (l:=(69/2:ℝ)) (u:=(42:ℝ))
    (by norm_num) hl hu (proof_representation_7).1 (proof_representation_7).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)

theorem improved_finite_log_ray (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (640000000000:ℝ) ≤ exp z) (hz42 : z ≤ 42) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hfirst : (6957/256:ℝ) ≤ z := by
    have h := first_log_below_cut.trans_le hcut
    exact (exp_lt_exp.mp h).le
  by_cases h0 : z ≤ (1743/64:ℝ)
  · exact improved_leaf_0_actual_gap hs hd hT hJ hL hU (by linarith) h0 hcut
  by_cases h1 : z ≤ (879/32:ℝ)
  · exact improved_leaf_1_actual_gap hs hd hT hJ hL hU (by linarith) h1 hcut
  by_cases h2 : z ≤ (1773/64:ℝ)
  · exact improved_leaf_2_actual_gap hs hd hT hJ hL hU (by linarith) h2 hcut
  by_cases h3 : z ≤ (447/16:ℝ)
  · exact improved_leaf_3_actual_gap hs hd hT hJ hL hU (by linarith) h3 hcut
  by_cases h4 : z ≤ (231/8:ℝ)
  · exact improved_leaf_4_actual_gap hs hd hT hJ hL hU (by linarith) h4 hcut
  by_cases h5 : z ≤ (123/4:ℝ)
  · exact improved_leaf_5_actual_gap hs hd hT hJ hL hU (by linarith) h5 hcut
  by_cases h6 : z ≤ (69/2:ℝ)
  · exact improved_leaf_6_actual_gap hs hd hT hJ hL hU (by linarith) h6 hcut
  exact improved_leaf_7_actual_gap hs hd hT hJ hL hU (by linarith) hz42 hcut

theorem ramanujan_640b_one_twentieth (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    (hs : LogIntegralSeriesIdentity IEANTN.li)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    (1/20:ℝ) ≤ RamStudy.RG x := by
  have hd := li_derivative_from_series hs
  have hx0 : 0 < x := by linarith
  by_cases hlog : log x ≤ 42
  · have hcut : (640000000000:ℝ) ≤ exp (log x) := by
      simpa only [exp_log hx0] using hx
    have h := improved_finite_log_ray hs hd hT hJ hL hU hcut hlog
    simpa only [exp_log hx0] using h
  · have h := RHTail.actual_RG_tail hRH hS hs (deriv_from_one_to_two hd)
      (l:=log x) (by linarith)
    have hweak : (1/20:ℝ) ≤ RamStudy.RG (exp (log x)) := by linarith
    simpa only [exp_log hx0] using hweak
#print axioms ramanujan_640b_one_twentieth
#check @ramanujan_640b_one_twentieth
end RHContinuation.Ramanujan
