import ActualSourceResult
import ActualDynamicTail
namespace RHContinuation.Ramanujan
open Real IEANTN Ramanujan640 Ramanujan640.RHTail
set_option maxHeartbeats 0

noncomputable def finalMargin (x : ℝ) : ℝ :=
  if exp 70 ≤ x then
    max (1+14/log x+144/(log x)^2) (dynamicBase (log x)-D a (log x))
  else if exp 42 ≤ x then
    max (4/5) (dynamicBase (log x)-D a (log x))
  else 1/12

/-- Full actual nonlinear profile, consuming source-model outputs and both
continuous tail envelopes, with precisely the original six analytic inputs. -/
theorem final_ramanujan_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) : finalMargin x ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  have transfer {A : ℝ} (hA : exp A ≤ x) : A ≤ log x := by
    apply exp_le_exp.mp
    simpa only [exp_log hx0] using hA
  unfold finalMargin
  split_ifs with h70 h42
  · have htail := actual_tail_144 hRH hS (transfer h70)
    have hfull := actual_dynamic_tail_profile hRH hS
      (by linarith [transfer h70] : (42:ℝ) ≤ log x)
    rw [exp_log hx0] at htail hfull
    exact max_le htail hfull
  · have htail := actual_tail_four_fifths hRH hS (transfer h42)
    have hfull := actual_dynamic_tail_profile hRH hS (transfer h42)
    rw [exp_log hx0] at htail hfull
    exact max_le htail hfull
  · exact source_ramanujan_640b hRH hT hJ hL hU hS hx

theorem final_gap_profile (hRH : SharedRH.hypothesis)
    (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (640000000000:ℝ) ≤ x) :
    finalMargin x*x^2/(log x)^6 ≤
      exp 1*x/log x*primeCounting (x/exp 1)-(primeCounting x)^2 := by
  have hr := final_ramanujan_profile hRH hT hJ hL hU hS hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6/x^2 := by positivity
  have he : (log x^6/x^2)*(finalMargin x*x^2/(log x)^6)=finalMargin x := by
    field_simp [hx0.ne',hl.ne']
  change finalMargin x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#print axioms final_ramanujan_profile
#print axioms final_gap_profile
#check @final_ramanujan_profile
end RHContinuation.Ramanujan
