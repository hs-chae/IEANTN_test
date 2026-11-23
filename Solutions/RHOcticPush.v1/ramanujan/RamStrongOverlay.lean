import RamFrontier607
import CorrStrongMid0
import CorrStrongHigh0
import CorrStrongHigh1
import CorrStrongHigh2
import CorrStrongHigh3
import CorrStrongHigh4
import CorrStrongHigh5
import CorrStrongHigh6
namespace RHOcticPush.Correlated
open Real Set IEANTN Ramanujan640 RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

theorem bridgeStrongMid_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (619000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 620000000000) :
    (1/100:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (27803/1024:ℝ) ≤ (619000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (27803/1024:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1779499/65536:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_620
    norm_num only [Real.log_exp] at h
    norm_num at h ⊢
    linarith
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  exact gapStrongMid_0_of_pair paired hTab hL hU (by linarith) hu hc hp

theorem bridgeStrongHigh_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/80:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (889749/32768:ℝ) ≤ (620000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (889749/32768:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1781579/65536:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_640
    norm_num only [Real.log_exp] at h
    norm_num at h ⊢
    linarith
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (113889953/4194304:ℝ)
  · exact gapStrongHigh_0_of_pair paired hTab hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (56946017/2097152:ℝ)
  · exact gapStrongHigh_1_of_pair paired hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (28474049/1048576:ℝ)
  · exact gapStrongHigh_2_of_pair paired hTab hL hU (by linarith) h2 hc hp
  by_cases h3 : z ≤ (14238065/524288:ℝ)
  · exact gapStrongHigh_3_of_pair paired hTab hL hU (by linarith) h3 hc hp
  by_cases h4 : z ≤ (7120073/262144:ℝ)
  · exact gapStrongHigh_4_of_pair paired hTab hL hU (by linarith) h4 hc hp
  by_cases h5 : z ≤ (3561077/131072:ℝ)
  · exact gapStrongHigh_5_of_pair paired hTab hL hU (by linarith) h5 hc hp
  exact gapStrongHigh_6_of_pair paired hTab hL hU (by linarith) hu hc hp

/-- Retain the frozen607 frontier and improve its619–640b bands. -/
noncomputable def strongFrontier607 (x : ℝ) : ℝ :=
  if (640000000000:ℝ) ≤ x then finalMargin x
  else if (620000000000:ℝ) ≤ x then 1/80
  else if (619000000000:ℝ) ≤ x then 1/100
  else frontier607 x

theorem actual_strong_frontier607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    strongFrontier607 x ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  unfold strongFrontier607
  split_ifs with h640 h620 h619
  · exact final_ramanujan_profile hRH hT2 hJ hL hU hS h640
  · have h := bridgeStrongHigh_of_pair paired hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h620)
      (by rw [exp_log hx0];linarith)
    simpa only [exp_log hx0] using h
  · have h := bridgeStrongMid_of_pair paired hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h619)
      (by rw [exp_log hx0];linarith)
    simpa only [exp_log hx0] using h
  · exact actual_frontier607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx

theorem actual_strong_frontier607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    strongFrontier607 x ≤ RamStudy.RG x :=
  actual_strong_frontier607_of_pair
    (fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx)
    hRH hGM hP hJ hT1 hT2 hL hU hS hx

lemma retains_full_original_strong {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    strongFrontier607 x=finalMargin x := by simp [strongFrontier607,hx]

lemma dominates_frozen_frontier (x : ℝ) : frontier607 x ≤ strongFrontier607 x := by
  unfold strongFrontier607
  split_ifs with h640 h620 h619
  · simp [frontier607,h640]
  · simp [frontier607,h640,h620] <;> norm_num
  · simp [frontier607,h640,h620,h619] <;> norm_num
  · exact le_rfl

theorem actual_strong_frontier_gap607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    strongFrontier607 x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hr := actual_strong_frontier607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(strongFrontier607 x*x^2/(log x)^6)=strongFrontier607 x := by
    field_simp [hx0.ne',hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_strong_frontier_strict607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have paired : PairTransfer :=
    fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx
  have h := actual_strong_frontier_gap607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < strongFrontier607 x := by
    unfold strongFrontier607 frontier607 finalMargin
    split_ifs <;> positivity
  have hp : 0 < strongFrontier607 x*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms bridgeStrongMid_of_pair
#print axioms bridgeStrongHigh_of_pair
#print axioms actual_strong_frontier607_of_pair
#print axioms actual_strong_frontier607
#print axioms actual_strong_frontier_gap607_of_pair
#print axioms dominates_frozen_frontier
#print axioms actual_strong_frontier_strict607
end RHOcticPush.Correlated
