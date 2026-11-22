import ActualTail
import ActualSourceFinite
namespace RHContinuation.Ramanujan
open Real IEANTN RamanujanPV.AnalyticTransition Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Stronger all-real result consuming all source-model degree20 outputs.
Only the coefficient component is source-first PV; finite envelope numerical
leaves use kernel interval proofs, and literature inputs remain explicit. -/
theorem source_ramanujan_640b (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    (1/12:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases hlog : log x ≤ 42
  · have hcut : (640000000000:ℝ) ≤ exp (log x) := by
      simpa only [exp_log hx0] using hx
    have h := source_finite_log_ray hT hJ hL hU hcut hlog
    simpa only [exp_log hx0] using h
  · have h := actual_tail_four_fifths hRH hS (l:=log x) (by linarith)
    have hweak : (1/12:ℝ) ≤ RamStudy.RG (exp (log x)) := by linarith
    simpa only [exp_log hx0] using hweak

noncomputable def sourceCertifiedMargin (x : ℝ) : ℝ :=
  if exp 42 ≤ x then 4/5 else 1/12

/-- The new whole-domain margin retains the stronger RH tail. -/
theorem source_ramanujan_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    sourceCertifiedMargin x ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  unfold sourceCertifiedMargin
  split_ifs with ht
  · have hl : (42:ℝ) ≤ log x := by
      apply exp_le_exp.mp
      simpa only [exp_log hx0] using ht
    simpa only [exp_log hx0] using actual_tail_four_fifths hRH hS hl
  · exact source_ramanujan_640b hRH hT hJ hL hU hS hx

/-- Quantitative nonlinear consumer for the actual prime-counting function. -/
theorem source_gap_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    sourceCertifiedMargin x*x^2/(log x)^6 ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := source_ramanujan_profile hRH hT hJ hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(sourceCertifiedMargin x*x^2/(log x)^6)=sourceCertifiedMargin x := by
    field_simp [hx0.ne',hl.ne']
  change sourceCertifiedMargin x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#print axioms source_ramanujan_640b
#print axioms source_ramanujan_profile
#print axioms source_gap_profile
#check @source_ramanujan_640b
#check @actual_tail_four_fifths
end RHContinuation.Ramanujan
