/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.GlobalReciprocal
namespace WinnerDensityA.Piecewise
open Real Set MeasureTheory Filter Topology CH2QRH
set_option maxHeartbeats 0
noncomputable def coefficient (c0 c1 c2 c3 a1 a2 a3 t : ℝ) :=
  if a3≤t then c3 else if a2≤t then c2 else if a1≤t then c1 else c0
noncomputable def stepMajorant (p q c0 c1 c2 c3 d a1 a2 a3 t : ℝ) :=
  coefficient c0 c1 c2 c3 a1 a2 a3 t*t^p*log t^q+d*log t^(2:ℕ)
noncomputable def cut (p q a t : ℝ) := if a≤t then integrand p q t else 0

theorem coefficient_decomposition {c0 c1 c2 c3 a1 a2 a3 t : ℝ}
    (h12 : a1≤a2) (h23 : a2≤a3) :
    coefficient c0 c1 c2 c3 a1 a2 a3 t=
      c0-(if a1≤t then c0-c1 else 0)-(if a2≤t then c1-c2 else 0)-
        (if a3≤t then c2-c3 else 0) := by
  by_cases h3 : a3≤t
  · have h2:=h23.trans h3
    have h1:=h12.trans h2
    simp only [coefficient,if_pos h3,if_pos h2,if_pos h1]
    ring
  · by_cases h2 : a2≤t
    · have h1:=h12.trans h2
      simp only [coefficient,if_neg h3,if_pos h2,if_pos h1]
      ring
    · by_cases h1 : a1≤t
      · simp only [coefficient,if_neg h3,if_neg h2,if_pos h1]
        ring
      · simp only [coefficient,if_neg h3,if_neg h2,if_neg h1,sub_zero]

theorem integrand_decomposition {p q c0 c1 c2 c3 d a1 a2 a3 : ℝ}
    (h12 : a1≤a2) (h23 : a2≤a3) :
    (fun t=>stepMajorant p q c0 c1 c2 c3 d a1 a2 a3 t/t^2)=
      fun t=>c0*integrand p q t-(c0-c1)*cut p q a1 t-
        (c1-c2)*cut p q a2 t-(c2-c3)*cut p q a3 t+d*integrand 0 2 t := by
  funext t
  unfold stepMajorant
  rw [coefficient_decomposition h12 h23]
  unfold cut integrand
  simp only [Real.rpow_zero,Real.rpow_two,one_mul]
  split_ifs <;> ring

 theorem cut_indicator (p q a : ℝ) : cut p q a=(Ici a).indicator (integrand p q) := by
  funext t
  simp only [cut,Set.indicator,Set.mem_Ici]

 theorem cut_integrable {p q A a : ℝ} (hi : IntegrableOn (integrand p q) (Ioi A)) :
    IntegrableOn (cut p q a) (Ioi A) := by
  rw [cut_indicator]
  exact hi.indicator measurableSet_Ici

 theorem cut_integral {p q A a : ℝ} (ha : A<a) :
    (∫t in Ioi A,cut p q a t)=∫t in Ioi a,integrand p q t := by
  rw [cut_indicator,integral_indicator measurableSet_Ici]
  rw [Measure.restrict_restrict measurableSet_Ici]
  have he : Ici a∩Ioi A=Ici a := by
    apply Set.inter_eq_left.mpr
    intro u hu
    exact ha.trans_le hu
  rw [he,integral_Ici_eq_integral_Ioi]

 theorem step_integrable {p q c0 c1 c2 c3 d A a1 a2 a3 : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : q≤4)
    (h12 : a1≤a2) (h23 : a2≤a3) :
    IntegrableOn (fun t=>stepMajorant p q c0 c1 c2 c3 d a1 a2 a3 t/t^2) (Ioi A) := by
  have hi:=integrand_integrable hA hl hp hp' hq
  have hj:=integrand_integrable hA hl (p:=0) (by norm_num) (by norm_num) (by norm_num : (2:ℝ)≤4)
  rw [integrand_decomposition h12 h23]
  exact ((((hi.const_mul c0).sub ((cut_integrable (a:=a1) hi).const_mul (c0-c1))).sub
    ((cut_integrable (a:=a2) hi).const_mul (c1-c2))).sub
    ((cut_integrable (a:=a3) hi).const_mul (c2-c3))).add (hj.const_mul d)

 theorem integral_step {p q c0 c1 c2 c3 d A a1 a2 a3 : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : q≤4)
    (ha1 : A<a1) (h12 : a1≤a2) (h23 : a2≤a3) :
    (∫t in Ioi A,stepMajorant p q c0 c1 c2 c3 d a1 a2 a3 t/t^2)=
      c0*(∫t in Ioi A,integrand p q t)-
      (c0-c1)*(∫t in Ioi a1,integrand p q t)-
      (c1-c2)*(∫t in Ioi a2,integrand p q t)-
      (c2-c3)*(∫t in Ioi a3,integrand p q t)+
      d*(∫t in Ioi A,integrand 0 2 t) := by
  have hi:=integrand_integrable hA hl hp hp' hq
  have hj:=integrand_integrable hA hl (p:=0) (by norm_num) (by norm_num) (by norm_num : (2:ℝ)≤4)
  have hi1:=(cut_integrable (a:=a1) hi).const_mul (c0-c1)
  have hi2:=(cut_integrable (a:=a2) hi).const_mul (c1-c2)
  have hi3:=(cut_integrable (a:=a3) hi).const_mul (c2-c3)
  rw [integrand_decomposition h12 h23]
  have e0:=integral_add ((((hi.const_mul c0).sub hi1).sub hi2).sub hi3) (hj.const_mul d)
  have e1:=integral_sub (((hi.const_mul c0).sub hi1).sub hi2) hi3
  have e2:=integral_sub ((hi.const_mul c0).sub hi1) hi2
  have e3:=integral_sub (hi.const_mul c0) hi1
  simp only [Pi.sub_apply] at e0 e1 e2 e3
  rw [e0,e1,e2,e3,
    integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul,
    cut_integral ha1,cut_integral (ha1.trans_le h12),cut_integral (ha1.trans_le (h12.trans h23))]

 theorem step_boundary_zero {p q c0 c1 c2 c3 d a1 a2 a3 : ℝ} (hp : p<1) :
    Tendsto (fun t=>stepMajorant p q c0 c1 c2 c3 d a1 a2 a3 t/t) atTop (𝓝 0) := by
  have h1:=(boundary_tendsto_zero (q:=q) hp).const_mul c3
  have h2:=(boundary_tendsto_zero (p:=0) (q:=2) (by norm_num)).const_mul d
  have hh:=h1.add h2
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop a3,eventually_gt_atTop (0:ℝ)] with t ht ht0
  rw [rpow_sub ht0,rpow_one,show (0:ℝ)-1=-1 by norm_num,rpow_neg_one,rpow_two]
  simp only [stepMajorant,coefficient,if_pos ht]
  ring

 theorem log_square_integral {A : ℝ} (hA : 1<A) (hl : 1≤log A) :
    (∫u in Ioi A,integrand 0 2 u)=(log A^(2:ℕ)+2*log A+2)/A := by
  have h0:=integral_identity hA hl (p:=0) (q:=0) (by norm_num) (by norm_num) (by norm_num)
  have h1:=integral_identity hA hl (p:=0) (q:=1) (by norm_num) (by norm_num) (by norm_num)
  have h2:=integral_identity hA hl (p:=0) (q:=2) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [zero_sub,sub_zero,sub_self,one_mul,zero_mul,add_zero,
    Real.rpow_zero,Real.rpow_one,Real.rpow_two,Real.rpow_neg_one] at h0 h1 h2
  have hA0 : A≠0 := (lt_trans zero_lt_one hA).ne'
  apply (eq_div_iff hA0).mpr
  field_simp [hA0] at h0 h1 h2
  nlinarith

/-- Closed four-height moment bound, with upper initial tail and LOWER
subtracted tails. Every subtraction sign is justified by monotone coefficients. -/
theorem step_integral_upper {p q c0 c1 c2 c3 d A a1 a2 a3 : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : 3≤q) (hq' : q≤4)
    (ha1 : A<a1) (h12 : a1≤a2) (h23 : a2≤a3)
    (hc0 : 0≤c0) (hc1 : c1≤c0) (hc2 : c2≤c1) (hc3 : c3≤c2)
    (hd : 0≤d) :
    (∫t in Ioi A,stepMajorant p q c0 c1 c2 c3 d a1 a2 a3 t/t^2)≤
      c0*upper p q A-(c0-c1)*lower p q a1-(c1-c2)*lower p q a2-
        (c2-c3)*lower p q a3+d*((log A^(2:ℕ)+2*log A+2)/A) := by
  have ha1' : 1<a1 := hA.trans ha1
  have ha2' : 1<a2 := ha1'.trans_le h12
  have ha3' : 1<a3 := ha2'.trans_le h23
  have hl1 : 1≤log a1 := hl.trans (log_le_log (by linarith) ha1.le)
  have hl2 : 1≤log a2 := hl1.trans (log_le_log (by linarith) h12)
  have hl3 : 1≤log a3 := hl2.trans (log_le_log (by linarith) h23)
  rw [integral_step hA hl hp hp' hq' ha1 h12 h23,log_square_integral hA hl]
  have h0:=mul_le_mul_of_nonneg_left (integral_upper hA hl hp hp' hq hq') hc0
  have h1:=mul_le_mul_of_nonneg_left (integral_lower ha1' hl1 hp hp' hq hq') (sub_nonneg.mpr hc1)
  have h2:=mul_le_mul_of_nonneg_left (integral_lower ha2' hl2 hp hp' hq hq') (sub_nonneg.mpr hc2)
  have h3:=mul_le_mul_of_nonneg_left (integral_lower ha3' hl3 hp hp' hq hq') (sub_nonneg.mpr hc3)
  linarith

#print axioms coefficient_decomposition
#print axioms integral_step
#print axioms step_boundary_zero
#print axioms step_integral_upper
end WinnerDensityA.Piecewise
