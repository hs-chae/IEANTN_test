import Corr607Result
import RamResult
namespace RHOcticPush.Correlated
open Real IEANTN Ramanujan640 RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- The strongest retained piecewise profile from BOTH completed methods. -/
noncomputable def frontier607 (x : ℝ) : ℝ :=
  if (640000000000:ℝ) ≤ x then finalMargin x
  else if (620000000000:ℝ) ≤ x then 1/400
  else if (619000000000:ℝ) ≤ x then 3/2000
  else if (610000000000:ℝ) ≤ x then 1/1000
  else 1/10000

theorem actual_frontier607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : frontier607 x ≤ RamStudy.RG x := by
  unfold frontier607
  split_ifs with h640 h620 h619 h610
  · exact final_ramanujan_profile hRH hT2 hJ hL hU hS h640
  · have h := RHOcticPush.Ram.actual_ramanujan_profile hRH hGM hP hJ hT1 hT2 hL hU hS
      (by linarith : (617500000000:ℝ) ≤ x)
    simpa only [RHOcticPush.Ram.certifiedMargin,if_neg h640,if_pos h620] using h
  · have h := RHOcticPush.Ram.actual_ramanujan_profile hRH hGM hP hJ hT1 hT2 hL hU hS
      (by linarith : (617500000000:ℝ) ≤ x)
    simpa only [RHOcticPush.Ram.certifiedMargin,if_neg h640,if_neg h620,if_pos h619] using h
  · exact actual_ramanujan_610b_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS h610
  · exact actual_ramanujan_607b_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx

theorem actual_frontier607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : frontier607 x ≤ RamStudy.RG x :=
  actual_frontier607_of_pair
    (fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx)
    hRH hGM hP hJ hT1 hT2 hL hU hS hx

lemma retains_full_original_frontier {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    frontier607 x=finalMargin x := by simp [frontier607,hx]

lemma dominates_uncoupled {x : ℝ} (hx : (617500000000:ℝ) ≤ x) :
    RHOcticPush.Ram.certifiedMargin x ≤ frontier607 x := by
  have h610 : (610000000000:ℝ) ≤ x := by linarith
  unfold RHOcticPush.Ram.certifiedMargin frontier607
  split_ifs <;> norm_num <;> linarith

lemma dominates_correlated {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    profile607 x ≤ frontier607 x := by
  unfold profile607 profile610 frontier607
  split_ifs <;> norm_num <;> linarith

theorem actual_frontier_gap607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    frontier607 x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hr := actual_frontier607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(frontier607 x*x^2/(log x)^6)=frontier607 x := by
    field_simp [hx0.ne',hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_frontier_strict607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have paired : PairTransfer :=
    fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx
  have h := actual_frontier_gap607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < frontier607 x := by
    unfold frontier607 finalMargin
    split_ifs <;> positivity
  have hp : 0 < frontier607 x*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms actual_frontier607_of_pair
#print axioms actual_frontier607
#print axioms actual_frontier_gap607_of_pair
#print axioms dominates_uncoupled
#print axioms dominates_correlated
#print axioms actual_frontier_strict607
end RHOcticPush.Correlated
