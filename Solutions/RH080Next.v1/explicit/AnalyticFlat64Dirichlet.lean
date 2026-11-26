/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace RH080Next.AnalyticFlat64

/-- Exact Dirichlet polynomial for the fixed64-flat nodal input. -/
def poly (t : ℝ) : ℝ := 1+2*∑ j ∈ Finset.Ico (1:ℕ) 64, cos (2*Real.pi*(j:ℝ)*t)

theorem continuous_poly : Continuous poly := by unfold poly; fun_prop

theorem poly_abs_le (t : ℝ) : |poly t|≤127 := by
  have hs : |∑ j ∈ Finset.Ico (1:ℕ) 64, cos (2*Real.pi*(j:ℝ)*t)|≤63 := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico (1:ℕ) 64, |cos (2*Real.pi*(j:ℝ)*t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico (1:ℕ) 64, (1:ℝ) := Finset.sum_le_sum (fun j _ => abs_cos_le_one _)
      _ = 63 := by norm_num
  calc
    |poly t| ≤ |(1:ℝ)|+|2*(∑ j ∈ Finset.Ico (1:ℕ) 64,cos (2*Real.pi*(j:ℝ)*t))| := abs_add_le _ _
    _ = 1+2*|∑ j ∈ Finset.Ico (1:ℕ) 64,cos (2*Real.pi*(j:ℝ)*t)| := by rw [abs_mul]; norm_num
    _ ≤ 127 := by linarith

theorem sin_mul_poly (t : ℝ) : sin (Real.pi*t)*poly t=sin (127*Real.pi*t) := by
  have h := Real.sin_mul_sum_cos 64 (2*Real.pi*t) 0
  have he (j : ℕ) : (2*Real.pi*t)*(j:ℝ)+0=2*Real.pi*(j:ℝ)*t := by ring
  simp_rw [he] at h
  have ha : (2*Real.pi*t)/2=Real.pi*t := by ring
  have hb : (64:ℝ)*(2*Real.pi*t)/2=64*Real.pi*t := by ring
  have hc : (63:ℝ)*(2*Real.pi*t)/2+0=63*Real.pi*t := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [ha,hb,hc] at h
  have hsum := Finset.sum_range_add_sum_Ico (fun j : ℕ=>cos (2*Real.pi*(j:ℝ)*t))
    (by norm_num : 1≤64)
  norm_num only [Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,cos_zero] at hsum
  have hh := Real.two_mul_sin_mul_cos (64*Real.pi*t) (63*Real.pi*t)
  rw [show 64*Real.pi*t-63*Real.pi*t=Real.pi*t by ring,
    show 64*Real.pi*t+63*Real.pi*t=127*Real.pi*t by ring] at hh
  rw [←hsum] at h
  dsimp [poly]
  nlinarith [h,hh]

theorem sin_positive_half (t : ℝ) (ht : 0<t) (htop : t≤1/2) : 0<sin (Real.pi*t) := by
  apply sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht)
  nlinarith [pi_pos]

theorem poly_abs_le_csc (t : ℝ) (ht : 0<t) (htop : t≤1/2) :
    |poly t|≤1/sin (Real.pi*t) := by
  have hsin := sin_positive_half t ht htop
  have h := congrArg abs (sin_mul_poly t)
  rw [abs_mul,abs_of_pos hsin] at h
  apply (le_div_iff₀ hsin).mpr
  nlinarith [abs_sin_le_one (127*Real.pi*t)]

theorem poly_reflect (t : ℝ) : poly (1-t)=poly t := by
  unfold poly
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [show 2*Real.pi*(j:ℝ)*(1-t)=(j:ℝ)*(2*Real.pi)-2*Real.pi*(j:ℝ)*t by ring,cos_sub,
    cos_nat_mul_two_pi,show sin ((j:ℝ)*(2*Real.pi)) = 0 by
      rw [show (j:ℝ)*(2*Real.pi)=((2*j:ℕ):ℝ)*Real.pi by push_cast; ring, sin_nat_mul_pi]]
  ring

theorem periodic_norm_eq_twice_half :
    (∫ t in (0:ℝ)..1,|poly t|)=2*(∫ t in (0:ℝ)..(1/2),|poly t|) := by
  have hi := continuous_poly.abs
  have href := intervalIntegral.integral_comp_sub_left (fun t : ℝ=>|poly t|)
    (a:=0) (b:=1/2) 1
  simp_rw [poly_reflect] at href
  norm_num only [sub_zero,show (1:ℝ)-1/2=1/2 by norm_num] at href
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable 0 (1/2)) (hi.intervalIntegrable (1/2) 1)]
  rw [←href]
  ring

#print axioms sin_mul_poly
#print axioms periodic_norm_eq_twice_half
end RH080Next.AnalyticFlat64
