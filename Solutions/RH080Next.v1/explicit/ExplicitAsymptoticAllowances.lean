/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAsymptoticWidth
import ExplicitPrimeWeights
import PrimePowerWindowBounds

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set Filter
open scoped Topology
namespace RH080Next.Explicit

theorem width_exp_tendsto (c a : ℝ) :
    Tendsto (fun t : ℝ => exp (a*halfLogWidth c t)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => a*halfLogWidth c t) atTop (𝓝 0) := by
    simpa using (halfLogWidth_tendsto_zero c).const_mul a
  simpa only [Function.comp_def,exp_zero] using (continuous_exp.tendsto 0).comp h

theorem width_linear_ratio_tendsto (c a : ℝ) :
    Tendsto (fun t : ℝ => (t+a*halfLogWidth c t)/t) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1+a*halfLogWidth c t/t) atTop (𝓝 1) := by
    have hd := ((halfLogWidth_tendsto_zero c).const_mul a).mul tendsto_inv_atTop_zero
    simpa only [mul_zero,zero_mul,add_zero,div_eq_mul_inv] using (tendsto_const_nhds (x := (1:ℝ))).add hd
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  field_simp

theorem width_two_linear_ratio_tendsto (c a b : ℝ) :
    Tendsto (fun t : ℝ => (t+a*halfLogWidth c t)/(t+b*halfLogWidth c t)) atTop (𝓝 1) := by
  have h := (width_linear_ratio_tendsto c a).div (width_linear_ratio_tendsto c b) one_ne_zero
  apply (show Tendsto (fun t : ℝ => ((t+a*halfLogWidth c t)/t)/((t+b*halfLogWidth c t)/t)) atTop (𝓝 1) by change Tendsto ((fun t : ℝ => (t+a*halfLogWidth c t)/t)/(fun t => (t+b*halfLogWidth c t)/t)) atTop (𝓝 1); simpa only [div_self one_ne_zero] using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact div_div_div_cancel_right₀ ht.ne' _ _

def eventualWingLead (c R t : ℝ) : ℝ :=
  2*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*halfLogWidth c t*
    exp ((t+halfLogWidth c t)+R*halfLogWidth c t)/log (exp ((t+halfLogWidth c t)/2))

def eventualWingEntrance (c R t : ℝ) : ℝ :=
  4*exteriorPrimeWeight (halfLogWidth c t) (t+halfLogWidth c t) R*
    exp ((t+halfLogWidth c t)/2)/log (exp ((t+halfLogWidth c t)/2))

/-- Exact identities retain the actual MV block ell=sqrt(exp(t+d)). -/
theorem eventual_wing_exact (c R t : ℝ) :
    eventualWingLead c R t = 4*poleScale c t*
      ((t+(1+R)*halfLogWidth c t)/(t+halfLogWidth c t))*exp ((3*R/2)*halfLogWidth c t) ∧
    eventualWingEntrance c R t = 8*((t+(1+R)*halfLogWidth c t)/(t+halfLogWidth c t))*exp ((R/2)*halfLogWidth c t) := by
  let d := halfLogWidth c t
  have he1 : exp ((t+d)+R*d)/exp (((t+d)-R*d)/2) =
      exp (t/2+d/2)*exp ((3*R/2)*d) := by
    rw [←exp_sub,←exp_add]
    congr 1
    dsimp [d]
    ring
  have he2 : exp ((t+d)/2)/exp (((t+d)-R*d)/2) = exp ((R/2)*d) := by
    rw [←exp_sub]
    congr 1
    ring
  constructor
  · unfold eventualWingLead exteriorPrimeWeight poleScale
    rw [log_exp]
    change 2*((t+d+R*d)/exp ((t+d-R*d)/2))*d*exp (t+d+R*d)/((t+d)/2) = _
    rw [show 2*((t+d+R*d)/exp ((t+d-R*d)/2))*d*exp (t+d+R*d)/((t+d)/2) =
      4*d*(t+d+R*d)/(t+d)*(exp (t+d+R*d)/exp ((t+d-R*d)/2)) by rw [div_div_eq_mul_div]; ring,he1]
    dsimp [d]
    ring
  · unfold eventualWingEntrance exteriorPrimeWeight
    rw [log_exp]
    change 4*((t+d+R*d)/exp ((t+d-R*d)/2))*exp ((t+d)/2)/((t+d)/2) = _
    rw [show 4*((t+d+R*d)/exp ((t+d-R*d)/2))*exp ((t+d)/2)/((t+d)/2) =
      8*(t+d+R*d)/(t+d)*(exp ((t+d)/2)/exp ((t+d-R*d)/2)) by rw [div_div_eq_mul_div]; ring,he2]
    dsimp [d]
    ring

theorem eventual_wing_lead_div_tendsto (c R : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => eventualWingLead c R t/t) atTop (𝓝 (2*c)) := by
  have h := (((poleScale_div_tendsto c hc).const_mul 4).mul
    (width_two_linear_ratio_tendsto c (1+R) 1)).mul (width_exp_tendsto c (3*R/2))
  have he : (4*(c/2)*1)*1 = 2*c := by ring
  rw [he] at h
  apply h.congr
  intro t
  rw [(eventual_wing_exact c R t).1]
  simp only [one_mul]
  ring

theorem eventual_wing_entrance_tendsto (c R : ℝ) :
    Tendsto (eventualWingEntrance c R) atTop (𝓝 8) := by
  have h := ((width_two_linear_ratio_tendsto c (1+R) 1).const_mul 8).mul (width_exp_tendsto c (R/2))
  have hh : Tendsto (fun t : ℝ => 8*((t+(1+R)*halfLogWidth c t)/(t+halfLogWidth c t))*exp ((R/2)*halfLogWidth c t)) atTop (𝓝 8) := by simpa using h
  exact hh.congr (fun t => (eventual_wing_exact c R t).2.symm)

theorem eventual_pole_loss_tendsto_zero (c mu : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => poleScale c t*(halfLogWidth c t/2)^2*mu) atTop (𝓝 0) := by
  have h := (((poleScale_div_tendsto c hc).mul (pow_mul_halfLogWidth_tendsto_zero c hc 1)).mul
    (halfLogWidth_tendsto_zero c)).const_mul (mu/4)
  have hh : Tendsto (fun t : ℝ => (mu/4)*((poleScale c t/t)*(t*halfLogWidth c t)*halfLogWidth c t)) atTop (𝓝 0) := by
    simpa only [pow_one,mul_zero,zero_mul] using h
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  field_simp
  <;> ring

/-- The complete proved prime-power allowance vanishes for arbitrary fixed
interval coefficient c. Its actual narrow-window root counting is retained. -/
theorem eventual_primepower_allowance_tendsto_zero (c R M : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => Primal.primePowerWindowAllowance M (t+halfLogWidth c t) (R*halfLogWidth c t)) atTop (𝓝 0) := by
  have hfirst := (pow_half_exp_tendsto_zero 2).mul (width_exp_tendsto c ((R-1)/2))
  have hsecond := ((pow_mul_halfLogWidth_tendsto_zero c hc 2).const_mul R).mul (width_exp_tendsto c R)
  have h := (((width_linear_ratio_tendsto c (1+R)).pow 2).mul (hfirst.add hsecond)).const_mul (M/(2*log 2))
  have hh : Tendsto (fun t : ℝ => M/(2*log 2)*(((t+(1+R)*halfLogWidth c t)/t)^2*
      (t^2*exp (-t/2)*exp (((R-1)/2)*halfLogWidth c t)+R*(t^2*halfLogWidth c t)*exp (R*halfLogWidth c t)))) atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,add_zero,one_pow] using h
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  let d := halfLogWidth c t
  have he1 : exp (-t/2)*exp (((R-1)/2)*d) = 1/exp (((t+d)-R*d)/2) := by
    rw [←exp_add,one_div,←exp_neg]
    congr 1
    ring
  have he2 : exp (R*d) = exp (((t+d)+R*d)/2)/exp (((t+d)-R*d)/2) := by
    rw [←exp_sub]
    congr 1
    ring
  change M/(2*log 2)*(((t+(1+R)*d)/t)^2*
    (t^2*exp (-t/2)*exp (((R-1)/2)*d)+R*(t^2*d)*exp (R*d))) = _
  rw [show t^2*exp (-t/2)*exp (((R-1)/2)*d) = t^2*(exp (-t/2)*exp (((R-1)/2)*d)) by ring,he1,he2]
  unfold Primal.primePowerWindowAllowance
  change _ = M*((t+d)+R*d)^2/(2*log 2*exp (((t+d)-R*d)/2))*(1+(R*d)*exp (((t+d)+R*d)/2))
  field_simp
  <;> ring

#print axioms eventual_wing_lead_div_tendsto
#print axioms eventual_wing_entrance_tendsto
#print axioms eventual_pole_loss_tendsto_zero
#print axioms eventual_primepower_allowance_tendsto_zero
end RH080Next.Explicit
