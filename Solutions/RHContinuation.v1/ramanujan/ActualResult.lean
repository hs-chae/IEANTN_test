import ActualTail
namespace RHContinuation.Ramanujan
open Real IEANTN RamanujanPV.AnalyticTransition Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Full all-real continuation result. All analytic facts about the actual
principal-value logarithmic integral are proved internally. -/
theorem actual_ramanujan_640b (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    (1/20:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases hlog : log x ≤ 42
  · have hcut : (640000000000:ℝ) ≤ exp (log x) := by
      simpa only [exp_log hx0] using hx
    have h := actual_finite_log_ray hT hJ hL hU hcut hlog
    simpa only [exp_log hx0] using h
  · have h := actual_tail_four_fifths hRH hS (l:=log x) (by linarith)
    have hweak : (1/20:ℝ) ≤ RamStudy.RG (exp (log x)) := by linarith
    simpa only [exp_log hx0] using hweak

noncomputable def certifiedMargin (x : ℝ) : ℝ :=
  if exp 42 ≤ x then 4/5 else 1/20

/-- The new whole-domain margin retains the stronger RH tail. -/
theorem actual_ramanujan_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    certifiedMargin x ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  unfold certifiedMargin
  split_ifs with ht
  · have hl : (42:ℝ) ≤ log x := by
      apply exp_le_exp.mp
      simpa only [exp_log hx0] using ht
    simpa only [exp_log hx0] using actual_tail_four_fifths hRH hS hl
  · exact actual_ramanujan_640b hRH hT hJ hL hU hS hx

/-- Quantitative nonlinear consumer for the actual prime-counting function. -/
theorem actual_gap_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    certifiedMargin x*x^2/(log x)^6 ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := actual_ramanujan_profile hRH hT hJ hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(certifiedMargin x*x^2/(log x)^6)=certifiedMargin x := by
    field_simp [hx0.ne',hl.ne']
  change certifiedMargin x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#print axioms actual_ramanujan_640b
#print axioms actual_ramanujan_profile
#print axioms actual_gap_profile
#check @actual_ramanujan_640b
#check @actual_tail_four_fifths
end RHContinuation.Ramanujan
