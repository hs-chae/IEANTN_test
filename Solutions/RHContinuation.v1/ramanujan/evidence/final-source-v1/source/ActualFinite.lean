import ActualPrimePowers
import FiniteConsumer
namespace RHContinuation.Ramanujan
open Real IEANTN RamanujanPV.AnalyticTransition Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def nd0 : ℝ := (939705288171/500000000000:ℝ)
theorem nd0_nonneg : (0:ℝ) ≤ nd0 := by norm_num [nd0]
theorem nd0_number : upper16 ((6957/256:ℝ)-1)+(19/25:ℝ) ≤ nd0 := by
  unfold upper16 ppExpSum p3 nd0
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_0 : (1/20:ℝ) ≤ endpointMargin (6957/256:ℝ) (1743/64:ℝ) c0 nd0 := by
  unfold endpointMargin c0 nd0
  interval_decide 80 (trust := kernel)

theorem actual_deficits_0 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c0 ≤ deficit z ∧ deficit (z-1) ≤ nd0 := by
  have hrow := leaf_0_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(6957/256:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_0_c_number
  have hnU := nd0_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_0

theorem actual_gap_0 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_0 hT hJ hL hU hl hu hcut
  exact actual_margin_0.trans (actual_slab_consumer (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ))
    (by norm_num) hl hu (proof_representation_0).1 nd0_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd1 : ℝ := (1878839145663/1000000000000:ℝ)
theorem nd1_nonneg : (0:ℝ) ≤ nd1 := by norm_num [nd1]
theorem nd1_number : upper16 ((1743/64:ℝ)-1)+(19/25:ℝ) ≤ nd1 := by
  unfold upper16 ppExpSum p3 nd1
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_1 : (1/20:ℝ) ≤ endpointMargin (1743/64:ℝ) (879/32:ℝ) c1 nd1 := by
  unfold endpointMargin c1 nd1
  interval_decide 80 (trust := kernel)

theorem actual_deficits_1 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c1 ≤ deficit z ∧ deficit (z-1) ≤ nd1 := by
  have hrow := leaf_1_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(1743/64:ℝ)) (u:=(879/32:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(1743/64:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_1_c_number
  have hnU := nd1_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_1

theorem actual_gap_1 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_1 hT hJ hL hU hl hu hcut
  exact actual_margin_1.trans (actual_slab_consumer (l:=(1743/64:ℝ)) (u:=(879/32:ℝ))
    (by norm_num) hl hu (proof_representation_1).1 nd1_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd2 : ℝ := (988304572827/500000000000:ℝ)
theorem nd2_nonneg : (0:ℝ) ≤ nd2 := by norm_num [nd2]
theorem nd2_number : upper16 ((879/32:ℝ)-1)+(43/50:ℝ) ≤ nd2 := by
  unfold upper16 ppExpSum p3 nd2
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_2 : (1/20:ℝ) ≤ endpointMargin (879/32:ℝ) (1773/64:ℝ) c2 nd2 := by
  unfold endpointMargin c2 nd2
  interval_decide 80 (trust := kernel)

theorem actual_deficits_2 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c2 ≤ deficit z ∧ deficit (z-1) ≤ nd2 := by
  have hrow := leaf_2_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(879/32:ℝ)) (u:=(1773/64:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(879/32:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_2_c_number
  have hnU := nd2_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_2

theorem actual_gap_2 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_2 hT hJ hL hU hl hu hcut
  exact actual_margin_2.trans (actual_slab_consumer (l:=(879/32:ℝ)) (u:=(1773/64:ℝ))
    (by norm_num) hl hu (proof_representation_2).1 nd2_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd3 : ℝ := (15795717609/8000000000:ℝ)
theorem nd3_nonneg : (0:ℝ) ≤ nd3 := by norm_num [nd3]
theorem nd3_number : upper16 ((1773/64:ℝ)-1)+(43/50:ℝ) ≤ nd3 := by
  unfold upper16 ppExpSum p3 nd3
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_3 : (1/20:ℝ) ≤ endpointMargin (1773/64:ℝ) (447/16:ℝ) c3 nd3 := by
  unfold endpointMargin c3 nd3
  interval_decide 80 (trust := kernel)

theorem actual_deficits_3 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c3 ≤ deficit z ∧ deficit (z-1) ≤ nd3 := by
  have hrow := leaf_3_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(1773/64:ℝ)) (u:=(447/16:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(1773/64:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_3_c_number
  have hnU := nd3_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_3

theorem actual_gap_3 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_3 hT hJ hL hU hl hu hcut
  exact actual_margin_3.trans (actual_slab_consumer (l:=(1773/64:ℝ)) (u:=(447/16:ℝ))
    (by norm_num) hl hu (proof_representation_3).1 nd3_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd4 : ℝ := (1972401268037/1000000000000:ℝ)
theorem nd4_nonneg : (0:ℝ) ≤ nd4 := by norm_num [nd4]
theorem nd4_number : upper16 ((447/16:ℝ)-1)+(43/50:ℝ) ≤ nd4 := by
  unfold upper16 ppExpSum p3 nd4
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_4 : (1/20:ℝ) ≤ endpointMargin (447/16:ℝ) (231/8:ℝ) c4 nd4 := by
  unfold endpointMargin c4 nd4
  interval_decide 80 (trust := kernel)

theorem actual_deficits_4 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c4 ≤ deficit z ∧ deficit (z-1) ≤ nd4 := by
  have hrow := leaf_4_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(447/16:ℝ)) (u:=(231/8:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(447/16:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_4_c_number
  have hnU := nd4_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_4

theorem actual_gap_4 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_4 hT hJ hL hU hl hu hcut
  exact actual_margin_4.trans (actual_slab_consumer (l:=(447/16:ℝ)) (u:=(231/8:ℝ))
    (by norm_num) hl hu (proof_representation_4).1 nd4_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd5 : ℝ := (199487668351/100000000000:ℝ)
theorem nd5_nonneg : (0:ℝ) ≤ nd5 := by norm_num [nd5]
theorem nd5_number : upper16 ((231/8:ℝ)-1)+(89/100:ℝ) ≤ nd5 := by
  unfold upper16 ppExpSum p3 nd5
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_5 : (1/20:ℝ) ≤ endpointMargin (231/8:ℝ) (123/4:ℝ) c5 nd5 := by
  unfold endpointMargin c5 nd5
  interval_decide 80 (trust := kernel)

theorem actual_deficits_5 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c5 ≤ deficit z ∧ deficit (z-1) ≤ nd5 := by
  have hrow := leaf_5_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(231/8:ℝ)) (u:=(123/4:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(231/8:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_5_c_number
  have hnU := nd5_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_5

theorem actual_gap_5 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_5 hT hJ hL hU hl hu hcut
  exact actual_margin_5.trans (actual_slab_consumer (l:=(231/8:ℝ)) (u:=(123/4:ℝ))
    (by norm_num) hl hu (proof_representation_5).1 nd5_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd6 : ℝ := (1046325446727/500000000000:ℝ)
theorem nd6_nonneg : (0:ℝ) ≤ nd6 := by norm_num [nd6]
theorem nd6_number : upper16 ((123/4:ℝ)-1)+(1:ℝ) ≤ nd6 := by
  unfold upper16 ppExpSum p3 nd6
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_6 : (1/20:ℝ) ≤ endpointMargin (123/4:ℝ) (69/2:ℝ) c6 nd6 := by
  unfold endpointMargin c6 nd6
  interval_decide 80 (trust := kernel)

theorem actual_deficits_6 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c6 ≤ deficit z ∧ deficit (z-1) ≤ nd6 := by
  have hrow := leaf_6_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(123/4:ℝ)) (u:=(69/2:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(123/4:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_6_c_number
  have hnU := nd6_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_6

theorem actual_gap_6 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_6 hT hJ hL hU hl hu hcut
  exact actual_margin_6.trans (actual_slab_consumer (l:=(123/4:ℝ)) (u:=(69/2:ℝ))
    (by norm_num) hl hu (proof_representation_6).1 nd6_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

noncomputable def nd7 : ℝ := (82225370003/40000000000:ℝ)
theorem nd7_nonneg : (0:ℝ) ≤ nd7 := by norm_num [nd7]
theorem nd7_number : upper16 ((69/2:ℝ)-1)+(49/50:ℝ) ≤ nd7 := by
  unfold upper16 ppExpSum p3 nd7
  norm_num only [Finset.sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
theorem actual_margin_7 : (1/20:ℝ) ≤ endpointMargin (69/2:ℝ) (42:ℝ) c7 nd7 := by
  unfold endpointMargin c7 nd7
  interval_decide 80 (trust := kernel)

theorem actual_deficits_7 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    c7 ≤ deficit z ∧ deficit (z-1) ≤ nd7 := by
  have hrow := leaf_7_riemann hT hJ hl hu hcut
  have hpL := pp_lower_slab hL (fun s h => (actual_p3_no_series h).1)
    (l:=(69/2:ℝ)) (u:=(42:ℝ)) (z:=z) (by norm_num) (by norm_num) hl hu
  have hpU := upper16_slab hU actual_global_no_series
    (fun s h => (actual_p3_no_series h).2) (l:=(69/2:ℝ)-1) (z:=z-1)
    (by norm_num) (by linarith) (by linarith)
  have hnL := proof_7_c_number
  have hnU := nd7_number
  have heL := deficit_split z
  have heU := deficit_split (z-1)
  constructor <;> linarith [hrow.1,hrow.2]
#print axioms actual_deficits_7

theorem actual_gap_7 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_7 hT hJ hL hU hl hu hcut
  exact actual_margin_7.trans (actual_slab_consumer (l:=(69/2:ℝ)) (u:=(42:ℝ))
    (by norm_num) hl hu (proof_representation_7).1 nd7_nonneg
    (actual_base_no_series (by linarith)) (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem actual_finite_log_ray (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (640000000000:ℝ) ≤ exp z) (hz42 : z ≤ 42) :
    (1/20:ℝ) ≤ RamStudy.RG (exp z) := by
  have hfirst : (6957/256:ℝ) ≤ z := by
    have h := first_log_below_cut.trans_le hcut
    exact (exp_lt_exp.mp h).le
  by_cases h0 : z ≤ (1743/64:ℝ)
  · exact actual_gap_0 hT hJ hL hU (by linarith) h0 hcut
  by_cases h1 : z ≤ (879/32:ℝ)
  · exact actual_gap_1 hT hJ hL hU (by linarith) h1 hcut
  by_cases h2 : z ≤ (1773/64:ℝ)
  · exact actual_gap_2 hT hJ hL hU (by linarith) h2 hcut
  by_cases h3 : z ≤ (447/16:ℝ)
  · exact actual_gap_3 hT hJ hL hU (by linarith) h3 hcut
  by_cases h4 : z ≤ (231/8:ℝ)
  · exact actual_gap_4 hT hJ hL hU (by linarith) h4 hcut
  by_cases h5 : z ≤ (123/4:ℝ)
  · exact actual_gap_5 hT hJ hL hU (by linarith) h5 hcut
  by_cases h6 : z ≤ (69/2:ℝ)
  · exact actual_gap_6 hT hJ hL hU (by linarith) h6 hcut
  exact actual_gap_7 hT hJ hL hU (by linarith) hz42 hcut

#print axioms actual_finite_log_ray
end RHContinuation.Ramanujan
