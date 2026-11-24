import Corr610Cell0
import Corr610Cell1
import Corr610Cell2
import Corr610Cell3
import RamBandMid
import ActualFinalProfile

/-! A complete all-real610b theorem from the original nine RH/literature inputs.
No .076 single-height spectral bound is assumed. The genuinely proved signed
two-height GM estimate supplies the missing margin. -/
namespace RHOcticPush.Correlated
open Real Set IEANTN Ramanujan640 RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

theorem bridge610 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (610000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 619000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (6947/256:ℝ) ≤ (610000000000:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : (6947/256:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1779393/65536:ℝ) := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_619
    norm_num only [Real.log_exp] at h
    norm_num at h ⊢
    linarith
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
  by_cases h0 : z ≤ (14228417/524288:ℝ)
  · exact gap610_0 hRH hGM hP hJ hTab hL hU hl h0 hc hp
  by_cases h1 : z ≤ (7114689/262144:ℝ)
  · exact gap610_1 hRH hGM hP hJ hTab hL hU (by linarith) h1 hc hp
  by_cases h2 : z ≤ (3557825/131072:ℝ)
  · exact gap610_2 hRH hGM hP hJ hTab hL hU (by linarith) h2 hc hp
  exact gap610_3 hRH hGM hP hJ hTab hL hU (by linarith) hu hc hp

theorem actual_ramanujan_610b (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (610000000000:ℝ) ≤ x) : (1/1000:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases h620 : (620000000000:ℝ) ≤ x
  · exact RHLimit.Ram620.actual_ramanujan_620b hRH hGM hP hJ hT1 hT2 hL hU hS h620
  by_cases h619 : (619000000000:ℝ) ≤ x
  · have h := RHOcticPush.Ram.bridge_mid hRH hGM hP hJ hT1 hL hU (z := log x)
      (by simpa only [exp_log hx0] using h619)
      (by rw [exp_log hx0]; linarith)
    rw [exp_log hx0] at h
    linarith
  have h := bridge610 hRH hGM hP hJ hT1 hL hU (z := log x)
    (by simpa only [exp_log hx0] using hx)
    (by rw [exp_log hx0]; linarith)
  simpa only [exp_log hx0] using h

noncomputable def profile610 (x : ℝ) : ℝ :=
  if (640000000000:ℝ) ≤ x then finalMargin x else 1/1000

theorem actual_profile610 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (610000000000:ℝ) ≤ x) : profile610 x ≤ RamStudy.RG x := by
  unfold profile610
  split_ifs with h640
  · exact final_ramanujan_profile hRH hT2 hJ hL hU hS h640
  · exact actual_ramanujan_610b hRH hGM hP hJ hT1 hT2 hL hU hS hx

theorem retains_full_original {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    profile610 x=finalMargin x := by simp [profile610,hx]

theorem actual_gap610 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (610000000000:ℝ) ≤ x) :
    profile610 x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hr := actual_profile610 hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(profile610 x*x^2/(log x)^6)=profile610 x := by
    field_simp [hx0.ne',hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

theorem actual_strict610 (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (610000000000:ℝ) ≤ x) :
    (primeCounting x)^2 < exp 1*x/log x*primeCounting (x/exp 1) := by
  have h := actual_gap610 hRH hGM hP hJ hT1 hT2 hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hm : 0 < profile610 x := by
    unfold profile610 finalMargin
    split_ifs <;> positivity
  have hp : 0 < profile610 x*x^2/(log x)^6 := by positivity
  unfold RamanujanGap.v1.gap at h
  linarith

#print axioms bridge610
#print axioms actual_ramanujan_610b
#print axioms actual_profile610
#print axioms actual_gap610
#print axioms actual_strict610
end RHOcticPush.Correlated
