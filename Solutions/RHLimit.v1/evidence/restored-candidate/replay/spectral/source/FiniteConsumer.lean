import RiemannBounds
import ProofBounds
import AnalyticBridges
namespace Ramanujan640
open Real IEANTN RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf_0_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c0 ≤ deficit z ∧ deficit (z-1) ≤ d0 := by
  have hrow := leaf_0_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(6957/256:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_0_c_number
  have hnU := proof_0_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_0_actual_deficits

theorem leaf_0_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_0_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_0_margin.trans (actual_slab_consumer (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ))
    (by norm_num) hl hu (proof_representation_0).1 (proof_representation_0).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_0_actual_gap

theorem leaf_1_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c1 ≤ deficit z ∧ deficit (z-1) ≤ d1 := by
  have hrow := leaf_1_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(1743/64:ℝ)) (u:=(879/32:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(1743/64:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_1_c_number
  have hnU := proof_1_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_1_actual_deficits

theorem leaf_1_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_1_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_1_margin.trans (actual_slab_consumer (l:=(1743/64:ℝ)) (u:=(879/32:ℝ))
    (by norm_num) hl hu (proof_representation_1).1 (proof_representation_1).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_1_actual_gap

theorem leaf_2_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c2 ≤ deficit z ∧ deficit (z-1) ≤ d2 := by
  have hrow := leaf_2_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(879/32:ℝ)) (u:=(1773/64:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(879/32:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_2_c_number
  have hnU := proof_2_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_2_actual_deficits

theorem leaf_2_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_2_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_2_margin.trans (actual_slab_consumer (l:=(879/32:ℝ)) (u:=(1773/64:ℝ))
    (by norm_num) hl hu (proof_representation_2).1 (proof_representation_2).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_2_actual_gap

theorem leaf_3_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c3 ≤ deficit z ∧ deficit (z-1) ≤ d3 := by
  have hrow := leaf_3_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(1773/64:ℝ)) (u:=(447/16:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(1773/64:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_3_c_number
  have hnU := proof_3_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_3_actual_deficits

theorem leaf_3_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_3_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_3_margin.trans (actual_slab_consumer (l:=(1773/64:ℝ)) (u:=(447/16:ℝ))
    (by norm_num) hl hu (proof_representation_3).1 (proof_representation_3).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_3_actual_gap

theorem leaf_4_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c4 ≤ deficit z ∧ deficit (z-1) ≤ d4 := by
  have hrow := leaf_4_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(447/16:ℝ)) (u:=(231/8:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(447/16:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_4_c_number
  have hnU := proof_4_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_4_actual_deficits

theorem leaf_4_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_4_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_4_margin.trans (actual_slab_consumer (l:=(447/16:ℝ)) (u:=(231/8:ℝ))
    (by norm_num) hl hu (proof_representation_4).1 (proof_representation_4).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_4_actual_gap

theorem leaf_5_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c5 ≤ deficit z ∧ deficit (z-1) ≤ d5 := by
  have hrow := leaf_5_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(231/8:ℝ)) (u:=(123/4:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(231/8:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_5_c_number
  have hnU := proof_5_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_5_actual_deficits

theorem leaf_5_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_5_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_5_margin.trans (actual_slab_consumer (l:=(231/8:ℝ)) (u:=(123/4:ℝ))
    (by norm_num) hl hu (proof_representation_5).1 (proof_representation_5).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_5_actual_gap

theorem leaf_6_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c6 ≤ deficit z ∧ deficit (z-1) ≤ d6 := by
  have hrow := leaf_6_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(123/4:ℝ)) (u:=(69/2:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(123/4:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_6_c_number
  have hnU := proof_6_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_6_actual_deficits

theorem leaf_6_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_6_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_6_margin.trans (actual_slab_consumer (l:=(123/4:ℝ)) (u:=(69/2:ℝ))
    (by norm_num) hl hu (proof_representation_6).1 (proof_representation_6).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_6_actual_gap

theorem leaf_7_actual_deficits (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c7 ≤ deficit z ∧ deficit (z-1) ≤ d7 := by
  have hrow := leaf_7_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_bounds hs hd h).1)
    (l:=(69/2:ℝ)) (u:=(42:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := pp_upper_slab hU (actual_global_w hs hd)
    (fun s h => (actual_p3_bounds hs hd h).2) (l:=(69/2:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_7_c_number
  have hnU := proof_7_d_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms leaf_7_actual_deficits

theorem leaf_7_actual_gap (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := leaf_7_actual_deficits hs hd hT hJ hL hU hl hu hcut
  exact proof_7_margin.trans (actual_slab_consumer (l:=(69/2:ℝ)) (u:=(42:ℝ))
    (by norm_num) hl hu (proof_representation_7).1 (proof_representation_7).2.2.2.1
    (actual_baseBound hs hd (by linarith)) (actual_w_p1 hs hd (by linarith)) hdef.1 hdef.2)
#print axioms leaf_7_actual_gap

theorem finite_log_ray (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (640000000000:ℝ) ≤ exp z) (hz42 : z ≤ 42) :
    (1/25:ℝ) ≤ RamStudy.RG (exp z) := by
  have hfirst : (6957/256:ℝ) ≤ z := by
    have h := first_log_below_cut.trans_le hcut
    exact (exp_lt_exp.mp h).le
  by_cases h0 : z ≤ (1743/64:ℝ)
  · exact leaf_0_actual_gap hs hd hT hJ hL hU (by linarith) h0 hcut
  by_cases h1 : z ≤ (879/32:ℝ)
  · exact leaf_1_actual_gap hs hd hT hJ hL hU (by linarith) h1 hcut
  by_cases h2 : z ≤ (1773/64:ℝ)
  · exact leaf_2_actual_gap hs hd hT hJ hL hU (by linarith) h2 hcut
  by_cases h3 : z ≤ (447/16:ℝ)
  · exact leaf_3_actual_gap hs hd hT hJ hL hU (by linarith) h3 hcut
  by_cases h4 : z ≤ (231/8:ℝ)
  · exact leaf_4_actual_gap hs hd hT hJ hL hU (by linarith) h4 hcut
  by_cases h5 : z ≤ (123/4:ℝ)
  · exact leaf_5_actual_gap hs hd hT hJ hL hU (by linarith) h5 hcut
  by_cases h6 : z ≤ (69/2:ℝ)
  · exact leaf_6_actual_gap hs hd hT hJ hL hU (by linarith) h6 hcut
  exact leaf_7_actual_gap hs hd hT hJ hL hU (by linarith) hz42 hcut
#print axioms finite_log_ray
end Ramanujan640
