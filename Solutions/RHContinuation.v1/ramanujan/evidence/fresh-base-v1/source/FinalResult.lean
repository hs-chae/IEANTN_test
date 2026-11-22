import FiniteConsumer
import RHTailActual640
namespace Ramanujan640
open Real IEANTN RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Post-lock kernel theorem for the unchanged900s640b claim.
The two standard li identities are explicit bridges to the principal-value
definition; no margin, certificate-success or analytic-barrier input is assumed. -/
theorem ramanujan_640b (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    (1/25:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases hlog : log x ≤ 42
  · have hcut : (640000000000:ℝ) ≤ exp (log x) := by
      simpa only [exp_log hx0] using hx
    have h := finite_log_ray hs hd hT hJ hL hU hcut hlog
    simpa only [exp_log hx0] using h
  · have h := RHTail.actual_RG_tail_one_twentyfifth hRH hS hs (deriv_from_one_to_two hd)
      (l:=log x) (by linarith)
    simpa only [exp_log hx0] using h

theorem actual_gap_640b (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    (hs : LogIntegralSeriesIdentity IEANTN.li)
    (hd : AnalyticBarrier.LiDerivativeFromOne IEANTN.li)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    x^2/(25*(log x)^6) ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := ramanujan_640b hRH hT hJ hL hU hS hs hd hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(x^2/(25*(log x)^6))=(1/25:ℝ) := by
    field_simp [hx0.ne',hl.ne']
  change x^2/(25*(log x)^6) ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#check ramanujan_640b
#print axioms ramanujan_640b
#print axioms actual_gap_640b
end Ramanujan640
