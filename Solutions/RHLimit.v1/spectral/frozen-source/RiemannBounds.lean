import TableTransport
import LeafDomains
namespace Ramanujan640
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem source_global_riemann (hB : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {s : ℝ} (hs : 1 ≤ s) (hs42 : s ≤ 42) :
    -1 ≤ riemannDeficit s ∧ riemannDeficit s ≤ 1 := by
  have h2 : 2 ≤ exp s := (exp_one_gt_two.le).trans (exp_le_exp.mpr hs)
  have h := hB (exp s) h2 ((exp_le_exp.mpr hs42).trans exp42_source_cap)
  rw [← exp_half, log_exp] at h
  have hp : 0 < s/exp (s/2) := by positivity
  have hm := mul_lt_mul_of_pos_right h hp
  have heL : |riemannDeficit s| = |li (exp s)-riemannPrimeCounting (exp s)| *(s/exp (s/2)) := by
    unfold riemannDeficit
    rw [abs_div,abs_mul,abs_of_pos (show 0 < s by linarith),abs_of_pos (exp_pos _)]
    ring
  have heR : exp (s/2)/s*(s/exp (s/2))=1 := by
    field_simp [show s ≠ 0 by linarith, exp_ne_zero]
  rw [← heL,heR] at hm
  exact ⟨(abs_lt.mp hm).1.le,(abs_lt.mp hm).2.le⟩
#print axioms source_global_riemann

theorem leaf_0_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-37/50:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (19/25:ℝ) := by
  have hd := frozen_leaf_0_domains hl hu hcut
  constructor
  · have h := lower_component_0 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_1 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_0_riemann

theorem leaf_1_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-37/50:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (19/25:ℝ) := by
  have hd := frozen_leaf_1_domains hl hu hcut
  constructor
  · have h := lower_component_0 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_1 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_1_riemann

theorem leaf_2_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-37/50:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (43/50:ℝ) := by
  have hd := frozen_leaf_2_domains hl hu hcut
  constructor
  · have h := lower_component_0 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_2 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_2_riemann

theorem leaf_3_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-22/25:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (43/50:ℝ) := by
  have hd := frozen_leaf_3_domains hl hu hcut
  constructor
  · have h := lower_component_3 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_2 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_3_riemann

theorem leaf_4_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-22/25:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (43/50:ℝ) := by
  have hd := frozen_leaf_4_domains hl hu hcut
  constructor
  · have h := lower_component_3 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_2 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_4_riemann

theorem leaf_5_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-87/100:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (89/100:ℝ) := by
  have hd := frozen_leaf_5_domains hl hu hcut
  constructor
  · have h := lower_component_4 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · have h := upper_component_5 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_5_riemann

theorem leaf_6_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-87/100:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (1:ℝ) := by
  have hd := frozen_leaf_6_domains hl hu hcut
  constructor
  · have h := lower_component_4 hT hd.1 hd.2.1
    simpa only [riemannDeficit,log_exp,← exp_half] using h
  · exact (source_global_riemann hB (by linarith) (by linarith)).2
#print axioms leaf_6_riemann

theorem leaf_7_riemann (hT : Buthe.v1.table_2_interval_bounds)
    (hB : Buthe.v1.theorem_2_li_minus_riemann_pi) {z : ℝ}
    (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ)) (hcut : (640000000000:ℝ) ≤ exp z) :
    (-1:ℝ) ≤ riemannDeficit z ∧ riemannDeficit (z-1) ≤ (49/50:ℝ) := by
  have hd := frozen_leaf_7_domains hl hu hcut
  constructor
  · exact (source_global_riemann hB (by linarith) (by linarith)).1
  · have h := upper_component_6 hT hd.2.2.1 hd.2.2.2
    simpa only [riemannDeficit,log_exp,← exp_half] using h
#print axioms leaf_7_riemann
end Ramanujan640
