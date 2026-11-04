/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Moment
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
namespace WinnerDensityA.Piecewise
open Real Set MeasureTheory Filter Topology CH2QRH
set_option maxHeartbeats 0
noncomputable def integrand (p q u : ℝ) := u^p*log u^q/u^2
noncomputable def upper (p q A : ℝ) :=
  A^(p-1)*log A^q/(1-p)*(1+q/((1-p)*log A)+
    q*(q-1)/((1-p)*log A)^2+q*(q-1)*(q-2)/((1-p)*log A)^3+
    q*(q-1)*(q-2)*(q-3)/((1-p)*log A)^4)
noncomputable def lower (p q A : ℝ) :=
  A^(p-1)*log A^q/(1-p)*(1+q/((1-p)*log A)+
    q*(q-1)/((1-p)*log A)^2+q*(q-1)*(q-2)/((1-p)*log A)^3)

theorem integrand_continuousOn {p q A : ℝ} (hA : 1<A) :
    ContinuousOn (integrand p q) (Ici A) := by
  intro u hu
  have hu1 : 1<u := hA.trans_le hu
  have hu0 : u≠0 := (lt_trans zero_lt_one hu1).ne'
  have hl : log u≠0 := (log_pos hu1).ne'
  unfold integrand
  exact (((Real.continuousAt_rpow_const u p (Or.inl hu0)).mul
    ((Real.continuousAt_log hu0).rpow_const (Or.inl hl))).div
    (continuousAt_id.pow 2) (pow_ne_zero _ hu0)).continuousWithinAt

/-- Integrability follows from the already proved finite four-step envelope;
there is no new infinite-integral assumption. -/
theorem integrand_integrable {p q A : ℝ} (hA : 1<A) (hl : 1≤log A)
    (hp : 0≤p) (hp' : p<1) (hq : q≤4) :
    IntegrableOn (integrand p q) (Ioi A) := by
  have hi4 : IntegrableOn (integrand p 4) (Ioi A) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (upper p 4 A) A
      (b:=fun t : ℝ => t) (l:=atTop) ?_ tendsto_id ?_
    · intro t
      by_cases hat : A≤t
      · exact (power_log_intervalIntegrable (p:=p) (q:=4) hA hat).1
      · have he : Ioc A t=∅ := Set.Ioc_eq_empty (not_lt.mpr (le_of_not_ge hat))
        rw [he]
        exact integrableOn_empty
    · filter_upwards [eventually_ge_atTop A] with t hat
      have hb := power_log_tail_four (p:=p) (q:=4) hA hat hp hp' (by norm_num) le_rfl
      have hnorm : (∫ u in A..t, ‖integrand p 4 u‖) = ∫ u in A..t, integrand p 4 u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hat] at hu
        have hu0 : 0<u := (lt_trans zero_lt_one hA).trans_le hu.1
        have hlu : 0<log u := log_pos (hA.trans_le hu.1)
        exact Real.norm_of_nonneg (by unfold integrand;positivity)
      rw [hnorm]
      change (∫ u in A..t, u^p*log u^4/u^2)≤upper p 4 A
      have hn : 0≤t^p*log t^(4:ℝ)/t := by
        have ht0 : 0<t := (lt_trans zero_lt_one hA).trans_le hat
        have hlt : 0<log t := log_pos (hA.trans_le hat)
        positivity
      exact (le_add_of_nonneg_left hn).trans hb
  refine hi4.mono' (((integrand_continuousOn (p:=p) (q:=q) hA).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0<u := (lt_trans zero_lt_one hA).trans hu
  have hlu : 1≤log u := hl.trans (log_le_log (by linarith) hu.le)
  have hr : log u^q≤log u^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le hlu hq
  rw [Real.norm_of_nonneg (by unfold integrand;positivity)]
  unfold integrand
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) (sq_nonneg u)

 theorem boundary_tendsto_zero {p q : ℝ} (hp : p<1) :
    Tendsto (fun u : ℝ => u^(p-1)*log u^q) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop q (show 0<1-p by linarith)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  rw [show p-1=-(1-p) by ring,Real.rpow_neg hu.le]
  ring


 theorem integral_upper {p q A : ℝ} (hA : 1<A) (hl : 1≤log A)
    (hp : 0≤p) (hp' : p<1) (hq : 3≤q) (hq' : q≤4) :
    (∫ u in Ioi A, integrand p q u)≤upper p q A := by
  have hi:=integrand_integrable hA hl hp hp' hq'
  have ht:=intervalIntegral_tendsto_integral_Ioi A hi tendsto_id
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop A] with t hat
  have hb:=power_log_tail_four hA hat hp hp' hq hq'
  have hn : 0≤t^p*log t^q/t := by
    have ht0 : 0<t := (lt_trans zero_lt_one hA).trans_le hat
    have hlt : 0<log t := log_pos (hA.trans_le hat)
    positivity
  exact (le_add_of_nonneg_left hn).trans hb

 theorem integral_identity {p q A : ℝ} (hA : 1<A) (hl : 1≤log A)
    (hp : 0≤p) (hp' : p<1) (hq : q≤4) :
    (1-p)*(∫ u in Ioi A,integrand p q u)=
      A^(p-1)*log A^q+q*(∫ u in Ioi A,integrand p (q-1) u) := by
  have hi:=integrand_integrable hA hl hp hp' hq
  have hj:=integrand_integrable hA hl hp hp' (show q-1≤4 by linarith)
  have hd : ∀ u∈Ici A,HasDerivAt (fun v:ℝ=>v^(p-1)*log v^q)
      (-(1-p)*integrand p q u+q*integrand p (q-1) u) u := by
    intro u hu
    exact hasDerivAt_power_log_moment (hA.trans_le hu)
  have he:=integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul (-(1-p))).add (hj.const_mul q)) (boundary_tendsto_zero (q:=q) hp')
  rw [integral_add (hi.const_mul (-(1-p))) (hj.const_mul q),
    integral_const_mul,integral_const_mul] at he
  linarith

 theorem integral_lower {p q A : ℝ} (hA : 1<A) (hl : 1≤log A)
    (hp : 0≤p) (hp' : p<1) (hq : 3≤q) (hq' : q≤4) :
    lower p q A≤∫ u in Ioi A,integrand p q u := by
  have hr : 0<1-p := by linarith
  have hl0 : 0<log A := by linarith
  let I : ℝ→ℝ := fun z=>∫u in Ioi A,integrand p z u
  let B : ℝ→ℝ := fun z=>A^(p-1)*log A^z/(1-p)
  have hid : ∀ z:ℝ,z≤4→I z=B z+z/(1-p)*I (z-1) := by
    intro z hz
    have hh:=integral_identity hA hl hp hp' hz
    dsimp only [I,B]
    rw [div_mul_eq_mul_div,←add_div]
    apply (eq_div_iff hr.ne').mpr
    nlinarith
  have hnon : 0≤I (q-4) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0<u := (lt_trans zero_lt_one hA).trans hu
    have hlu : 0<log u := log_pos (hA.trans hu)
    unfold integrand
    positivity
  have h3 : B (q-3)≤I (q-3) := by
    rw [hid (q-3) (by linarith)]
    have hcoef : 0≤(q-3)/(1-p) := div_nonneg (by linarith) hr.le
    have heq : q-3-1=q-4 := by ring
    rw [heq]
    nlinarith
  have he1 : q-1-1=q-2 := by ring
  have he2 : q-2-1=q-3 := by ring
  have hbound : B q+q/(1-p)*(B (q-1)+(q-1)/(1-p)*(B (q-2)+(q-2)/(1-p)*B (q-3)))≤I q := by
    rw [hid q hq',hid (q-1) (by linarith),he1,hid (q-2) (by linarith),he2]
    gcongr <;> exact div_nonneg (by linarith) hr.le
  apply le_trans _ hbound
  apply le_of_eq
  unfold lower B
  rw [Real.rpow_sub hl0,Real.rpow_sub hl0,Real.rpow_sub hl0,
    Real.rpow_one,Real.rpow_two,show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast]
  field_simp
  <;> ring

#print axioms integrand_integrable
#print axioms boundary_tendsto_zero
#print axioms integral_upper
#print axioms integral_lower
end WinnerDensityA.Piecewise
