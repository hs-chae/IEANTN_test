/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSActualCutoff
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

def qDensity (x : ℝ) : ℝ:=log (x/(2*π))/(2*π)

theorem cmsQ_formula (x : ℝ) : cmsQ x=x/(2*π)*(log (x/(2*π))-1)+7/8:=by
  by_cases zero : x=0
  · simp [zero,cmsQ]
  unfold cmsQ
  have arg : x/(2*π*exp 1)=(x/(2*π))/exp 1:=by rw [div_div]
  rw [arg,log_div (div_ne_zero zero (by positivity)) (exp_ne_zero 1),log_exp]

theorem cmsQ_hasDerivAt (x : ℝ) (hx : x≠0) : HasDerivAt cmsQ (qDensity x) x:=by
  have denominator : (2*π:ℝ)≠0:=by positivity
  have linear:= (hasDerivAt_id x).div_const (2*π)
  have logarithm:=linear.log (div_ne_zero hx denominator)
  have product:=(linear.mul (logarithm.sub_const 1)).add_const (7/8:ℝ)
  have formula : cmsQ=(fun y : ℝ=> y/(2*π)*(log (y/(2*π))-1)+7/8):=funext cmsQ_formula
  have scalar : 1/(2*π)*(log (x/(2*π))-1)+x/(2*π)*(1/(2*π)/(x/(2*π)))=qDensity x:=by
    unfold qDensity
    field_simp [hx,denominator]
    <;> ring
  rw [formula,←scalar]
  simpa only [id_eq,Pi.mul_apply] using product

theorem q_continuousOn (a T : ℝ) (ha : 0< a) : ContinuousOn cmsQ (Icc a T):=by
  intro x hx
  exact (cmsQ_hasDerivAt x (ne_of_gt (lt_of_lt_of_le ha hx.1))).continuousAt.continuousWithinAt

theorem qDensity_continuousOn (a T : ℝ) (ha : 0< a) : ContinuousOn qDensity (Icc a T):=by
  intro x hx
  have nonzero : x/(2*π)≠0:=div_ne_zero (ne_of_gt (lt_of_lt_of_le ha hx.1)) (by positivity)
  unfold qDensity
  fun_prop

/-- The smooth comparison term is integrated by parts separately at finite T;
no divergent integral of N(t)|g'(t)| on the whole half-line is introduced. -/
theorem q_cutoff_ibp (a T : ℝ) (ha : 0< a) (hab : a≤ T)
    (g g' : ℝ → ℝ) (hd : ∀x,HasDerivAt g (g' x) x) (hc : Continuous g') :
    IntegrableOn (fun t=> cmsQ t*g' t) (Ioc a T) ∧
      IntegrableOn (fun t=> qDensity t*g t) (Ioc a T) ∧
      (∫t in Ioc a T,cmsQ t*g' t)=cmsQ T*g T-cmsQ a*g a-∫t in Ioc a T,qDensity t*g t:=by
  have gc : Continuous g:=continuous_iff_continuousAt.mpr (fun x=>(hd x).continuousAt)
  have qcont:=q_continuousOn a T ha
  have qpcont:=qDensity_continuousOn a T ha
  have formula:=intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u:=cmsQ) (u':=qDensity) (v:=g) (v':=g')
    (by simpa only [uIcc_of_le hab] using qcont) gc.continuousOn
    (fun x hx=> cmsQ_hasDerivAt x (by rw [min_eq_left hab,max_eq_right hab] at hx;exact ne_of_gt (lt_trans ha hx.1)))
    (fun x _=> hd x) (qpcont.intervalIntegrable_of_Icc hab) (hc.intervalIntegrable a T)
  simp_rw [intervalIntegral.integral_of_le hab] at formula
  exact ⟨(qcont.mul hc.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self,
    (qpcont.mul gc.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self,formula⟩

#print axioms cmsQ_hasDerivAt
#print axioms q_cutoff_ibp
end RH080Next.Explicit.ZeroSummation
