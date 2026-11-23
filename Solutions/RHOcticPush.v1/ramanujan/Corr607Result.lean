import Corr607Cell0
import Corr607Cell1
import Corr607Cell2
import Corr607Cell3
import Corr607Cell4
import Corr607Cell5
import Corr607Cell6
namespace RHOcticPush.Correlated
open Real Set IEANTN Ramanujan640 RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

theorem bridge607_of_pair (paired : PairTransfer)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (607000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 610000000000) :
    (1/10000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (1778109/65536:ℝ) ≤ (607000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (1778109/65536:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1778433/65536:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_610
    norm_num only [Real.log_exp] at h
    norm_num at h ⊢
    linarith
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (28449825/1048576:ℝ)
  · exact gap607_0_of_pair paired hTab hL hU (by linarith) h0 hc hp
  by_cases h1 : z ≤ (14224953/524288:ℝ)
  · exact gap607_1_of_pair paired hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (7112517/262144:ℝ)
  · exact gap607_2_of_pair paired hTab hL hU (by linarith) h2 hc hp
  by_cases h3 : z ≤ (3556299/131072:ℝ)
  · exact gap607_3_of_pair paired hTab hL hU (by linarith) h3 hc hp
  by_cases h4 : z ≤ (889095/32768:ℝ)
  · exact gap607_4_of_pair paired hTab hL hU (by linarith) h4 hc hp
  by_cases h5 : z ≤ (1778271/65536:ℝ)
  · exact gap607_5_of_pair paired hTab hL hU (by linarith) h5 hc hp
  exact gap607_6_of_pair paired hTab hL hU (by linarith) hu hc hp

/-- Actual607b frontier; the typed paired node is genuinely consumed. -/
theorem actual_ramanujan_607b_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : (1/10000:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases h610 : (610000000000:ℝ) ≤ x
  · have h := actual_ramanujan_610b_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS h610
    linarith
  have h := bridge607_of_pair paired hT1 hL hU (z := log x)
    (by simpa only [exp_log hx0] using hx)
    (by rw [exp_log hx0]; linarith)
  simpa only [exp_log hx0] using h

theorem actual_ramanujan_607b (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : (1/10000:ℝ) ≤ RamStudy.RG x :=
  actual_ramanujan_607b_of_pair
    (fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx)
    hRH hGM hP hJ hT1 hT2 hL hU hS hx

noncomputable def profile607 (x : ℝ) : ℝ :=
  if (610000000000:ℝ) ≤ x then profile610 x else 1/10000

theorem actual_profile607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : profile607 x ≤ RamStudy.RG x := by
  unfold profile607
  split_ifs with h610
  · unfold profile610
    split_ifs with h640
    · exact final_ramanujan_profile hRH hT2 hJ hL hU hS h640
    · exact actual_ramanujan_610b_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS h610
  · exact actual_ramanujan_607b_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx

theorem actual_profile607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) : profile607 x ≤ RamStudy.RG x :=
  actual_profile607_of_pair
    (fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx)
    hRH hGM hP hJ hT1 hT2 hL hU hS hx

lemma retains610 {x : ℝ} (hx : (610000000000:ℝ) ≤ x) :
    profile607 x=profile610 x := by simp [profile607,hx]

lemma retains_full_original607 {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    profile607 x=finalMargin x := by
  rw [retains610 (by linarith),retains_full_original hx]

theorem actual_gap607_of_pair (paired : PairTransfer) (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    profile607 x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hr := actual_profile607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(profile607 x*x^2/(log x)^6)=profile607 x := by
    field_simp [hx0.ne',hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_strict607 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (607000000000:ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have paired : PairTransfer :=
    fun _ _ _ hk0 hke hy hyx => GM.actual_pair_upper hRH hGM hP hJ hk0 hke hy hyx
  have h := actual_gap607_of_pair paired hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < profile607 x := by
    unfold profile607 profile610 finalMargin
    split_ifs <;> positivity
  have hp : 0 < profile607 x*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms bridge607_of_pair
#print axioms actual_ramanujan_607b
#print axioms actual_profile607_of_pair
#print axioms actual_gap607_of_pair
#print axioms actual_strict607
end RHOcticPush.Correlated
