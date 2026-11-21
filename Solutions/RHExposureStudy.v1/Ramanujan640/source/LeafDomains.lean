import LeafMargins
namespace Ramanujan640
open Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

theorem frozen_leaf_0_domains {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (640000000000:ℝ) ≤ exp z ∧ exp z ≤ (1280000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (320000000000:ℝ) := by
  have ha := hcut
  have hbn : exp (1743/64:ℝ) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((6957/256:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (6957/256:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((1743/64:ℝ)-1) ≤ (320000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (1743/64:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_0_domains

theorem frozen_leaf_1_domains {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (640000000000:ℝ) ≤ exp z ∧ exp z ≤ (1280000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (320000000000:ℝ) := by
  have ha := hcut
  have hbn : exp (879/32:ℝ) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((1743/64:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (1743/64:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((879/32:ℝ)-1) ≤ (320000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (879/32:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_1_domains

theorem frozen_leaf_2_domains {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (640000000000:ℝ) ≤ exp z ∧ exp z ≤ (1280000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (1280000000000:ℝ) := by
  have ha := hcut
  have hbn : exp (1773/64:ℝ) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((879/32:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (879/32:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((1773/64:ℝ)-1) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (1773/64:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_2_domains

theorem frozen_leaf_3_domains {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (640000000000:ℝ) ≤ exp z ∧ exp z ≤ (12800000000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (1280000000000:ℝ) := by
  have ha := hcut
  have hbn : exp (447/16:ℝ) ≤ (12800000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((1773/64:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (1773/64:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((447/16:ℝ)-1) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (447/16:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_3_domains

theorem frozen_leaf_4_domains {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (640000000000:ℝ) ≤ exp z ∧ exp z ≤ (12800000000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (1280000000000:ℝ) := by
  have ha := hcut
  have hbn : exp (231/8:ℝ) ≤ (12800000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((447/16:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (447/16:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((231/8:ℝ)-1) ≤ (1280000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (231/8:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_4_domains

theorem frozen_leaf_5_domains {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (2000000000000:ℝ) ≤ exp z ∧ exp z ≤ (12800000000000000:ℝ) ∧
    (160000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (32000000000000:ℝ) := by
  have han : (2000000000000:ℝ) ≤ exp (231/8:ℝ) := by interval_decide 60 (trust := kernel)
  have ha := han.trans (exp_le_exp.mpr hl)
  have hbn : exp (123/4:ℝ) ≤ (12800000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (160000000000:ℝ) ≤ exp ((231/8:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (231/8:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((123/4:ℝ)-1) ≤ (32000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (123/4:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_5_domains

theorem frozen_leaf_6_domains {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (2000000000000:ℝ) ≤ exp z ∧ exp z ≤ (12800000000000000:ℝ) ∧
    (2:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (10000000000000000000:ℝ) := by
  have han : (2000000000000:ℝ) ≤ exp (123/4:ℝ) := by interval_decide 60 (trust := kernel)
  have ha := han.trans (exp_le_exp.mpr hl)
  have hbn : exp (69/2:ℝ) ≤ (12800000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (2:ℝ) ≤ exp ((123/4:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (123/4:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((69/2:ℝ)-1) ≤ (10000000000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (69/2:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_6_domains

theorem frozen_leaf_7_domains {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (2:ℝ) ≤ exp z ∧ exp z ≤ (10000000000000000000:ℝ) ∧
    (64000000000000:ℝ) ≤ exp (z-1) ∧ exp (z-1) ≤ (5120000000000000000:ℝ) := by
  have han : (2:ℝ) ≤ exp (69/2:ℝ) := by interval_decide 60 (trust := kernel)
  have ha := han.trans (exp_le_exp.mpr hl)
  have hbn : exp (42:ℝ) ≤ (10000000000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hb := (exp_le_exp.mpr hu).trans hbn
  have hcn : (64000000000000:ℝ) ≤ exp ((69/2:ℝ)-1) := by interval_decide 60 (trust := kernel)
  have hc := hcn.trans (exp_le_exp.mpr (show (69/2:ℝ)-1 ≤ z-1 by linarith))
  have hdn : exp ((42:ℝ)-1) ≤ (5120000000000000000:ℝ) := by interval_decide 60 (trust := kernel)
  have hd := (exp_le_exp.mpr (show z-1 ≤ (42:ℝ)-1 by linarith)).trans hdn
  exact ⟨ha,hb,hc,hd⟩
#print axioms frozen_leaf_7_domains
end Ramanujan640
