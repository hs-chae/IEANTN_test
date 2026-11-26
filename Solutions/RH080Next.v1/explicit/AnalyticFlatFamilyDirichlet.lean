/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlat64Integral
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace RH080Next.AnalyticFlatFamily

def order (m:ℕ) : ℝ :=2*(m:ℝ)-1
def poly (m:ℕ) (t:ℝ):ℝ :=1+2*∑j∈Finset.Ico (1:ℕ) m,cos (2*Real.pi*(j:ℝ)*t)

theorem order_ge_one (m:ℕ) (hm:0<m):1≤order m :=by
  have h : (1:ℝ)≤(m:ℝ) :=by exact_mod_cast hm
  unfold order
  linarith

theorem continuous_poly (m:ℕ):Continuous (poly m):=by unfold poly;fun_prop

theorem poly_abs_le (m:ℕ) (hm:0<m) (t:ℝ):|poly m t|≤order m:=by
  have hs : |∑j∈Finset.Ico (1:ℕ) m,cos (2*Real.pi*(j:ℝ)*t)|≤(m-1:ℕ):=by
    calc
      _≤∑j∈Finset.Ico (1:ℕ) m,|cos (2*Real.pi*(j:ℝ)*t)|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑j∈Finset.Ico (1:ℕ) m,(1:ℝ):=Finset.sum_le_sum (fun j _=>abs_cos_le_one _)
      _=(m-1:ℕ):=by simp
  have hsub : ((m-1:ℕ):ℝ)=(m:ℝ)-1:=by rw[Nat.cast_sub (by omega)];norm_num
  calc
    |poly m t|≤|(1:ℝ)|+|2*∑j∈Finset.Ico (1:ℕ) m,cos (2*Real.pi*(j:ℝ)*t)|:=abs_add_le _ _
    _=1+2*|∑j∈Finset.Ico (1:ℕ) m,cos (2*Real.pi*(j:ℝ)*t)|:=by rw[abs_mul];norm_num
    _≤order m:=by rw[hsub] at hs;unfold order;linarith

theorem sin_mul_poly (m:ℕ) (hm:0<m) (t:ℝ):
    sin (Real.pi*t)*poly m t=sin (order m*Real.pi*t):=by
  have h:=Real.sin_mul_sum_cos m (2*Real.pi*t) 0
  have he (j:ℕ):(2*Real.pi*t)*(j:ℝ)+0=2*Real.pi*(j:ℝ)*t:=by ring
  simp_rw[he] at h
  have ha:(2*Real.pi*t)/2=Real.pi*t:=by ring
  have hb:(m:ℝ)*(2*Real.pi*t)/2=(m:ℝ)*Real.pi*t:=by ring
  have hc:((m:ℝ)-1)*(2*Real.pi*t)/2+0=((m:ℝ)-1)*Real.pi*t:=by ring
  rw[ha,hb,hc] at h
  have hsum:=Finset.sum_range_add_sum_Ico (fun j:ℕ=>cos (2*Real.pi*(j:ℝ)*t)) (by omega:1≤m)
  norm_num only[Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,cos_zero] at hsum
  rw[←hsum] at h
  have hh:=Real.two_mul_sin_mul_cos ((m:ℝ)*Real.pi*t) (((m:ℝ)-1)*Real.pi*t)
  rw[show (m:ℝ)*Real.pi*t-((m:ℝ)-1)*Real.pi*t=Real.pi*t by ring,
    show (m:ℝ)*Real.pi*t+((m:ℝ)-1)*Real.pi*t=order m*Real.pi*t by unfold order;ring] at hh
  unfold poly
  nlinarith[h,hh]

theorem poly_abs_le_csc (m:ℕ) (hm:0<m) (t:ℝ) (ht:0<t) (htop:t≤1/2):
    |poly m t|≤1/sin (Real.pi*t):=by
  have hsin:=RH080Next.AnalyticFlat64.sin_positive_half t ht htop
  have h:=congrArg abs (sin_mul_poly m hm t)
  rw[abs_mul,abs_of_pos hsin] at h
  apply (le_div_iff₀ hsin).mpr
  nlinarith[abs_sin_le_one (order m*Real.pi*t)]

theorem poly_reflect (m:ℕ) (t:ℝ):poly m (1-t)=poly m t:=by
  unfold poly
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw[show 2*Real.pi*(j:ℝ)*(1-t)=(j:ℝ)*(2*Real.pi)-2*Real.pi*(j:ℝ)*t by ring,
    cos_sub,cos_nat_mul_two_pi,
    show sin ((j:ℝ)*(2*Real.pi))=0 by rw[show (j:ℝ)*(2*Real.pi)=((2*j:ℕ):ℝ)*Real.pi by push_cast;ring,sin_nat_mul_pi]]
  ring

theorem periodic_norm_eq_twice_half (m:ℕ):
    (∫t in (0:ℝ)..1,|poly m t|)=2*(∫t in (0:ℝ)..(1/2),|poly m t|):=by
  have hi:=(continuous_poly m).abs
  have href:=intervalIntegral.integral_comp_sub_left (fun t:ℝ=>|poly m t|) (a:=0) (b:=1/2) 1
  simp_rw[poly_reflect] at href
  norm_num only[sub_zero,show (1:ℝ)-1/2=1/2 by norm_num] at href
  rw[←intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable 0 (1/2)) (hi.intervalIntegrable (1/2) 1),←href]
  ring

#print axioms sin_mul_poly
end RH080Next.AnalyticFlatFamily
