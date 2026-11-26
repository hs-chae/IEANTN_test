/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlat64Dirichlet
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace RH080Next.AnalyticFlat64

def cut : ℝ := 1/(127*Real.pi)
def cscPrimitive (t : ℝ) : ℝ := log (tan (Real.pi*t/2))/Real.pi

theorem cut_pos : 0<cut := by unfold cut; positivity

theorem cut_le_half : cut≤1/2 := by
  unfold cut
  apply (div_le_iff₀ (by positivity : (0:ℝ)<127*Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

theorem half_angle_pos (t : ℝ) (ht : 0<t) (htop : t≤1/2) :
    0<Real.pi*t/2 ∧ Real.pi*t/2<Real.pi/2 := by
  constructor
  · positivity
  · nlinarith [Real.pi_pos]

theorem cscPrimitive_hasDerivAt (t : ℝ) (ht : 0<t) (htop : t≤1/2) :
    HasDerivAt cscPrimitive (1/sin (Real.pi*t)) t := by
  have hp := half_angle_pos t ht htop
  have hcos : 0<cos (Real.pi*t/2) :=
    cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hp.2⟩
  have hsin : 0<sin (Real.pi*t/2) :=
    sin_pos_of_pos_of_lt_pi hp.1 (by linarith [Real.pi_pos])
  have htan : 0<tan (Real.pi*t/2) := tan_pos_of_pos_of_lt_pi_div_two hp.1 hp.2
  have hd : HasDerivAt (fun x : ℝ=>Real.pi*x/2) (Real.pi/2) t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul Real.pi).div_const 2
  have hdTan : HasDerivAt (fun x : ℝ=>tan (Real.pi*x/2))
      ((1/cos (Real.pi*t/2)^2)*(Real.pi/2)) t := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_tan hcos.ne').comp t hd
  have h := (hdTan.log htan.ne').div_const Real.pi
  have hv : ((1/cos (Real.pi*t/2)^2)*(Real.pi/2)/tan (Real.pi*t/2))/Real.pi =
      1/sin (Real.pi*t) := by
    rw [show Real.pi*t=2*(Real.pi*t/2) by ring,Real.sin_two_mul,Real.tan_eq_sin_div_cos]
    field_simp
  rw [hv] at h
  convert! h using 1

theorem integral_csc_cut_half :
    (∫ t in cut..(1/2:ℝ), 1/sin (Real.pi*t))≤log 254/Real.pi := by
  have hcont : ContinuousOn (fun t : ℝ=>1/sin (Real.pi*t)) (Set.Icc cut (1/2)) := by
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (sin_positive_half t (lt_of_lt_of_le cut_pos ht.1) ht.2).ne'
  have hint : IntervalIntegrable (fun t : ℝ=>1/sin (Real.pi*t)) volume cut (1/2) := by
    apply hcont.intervalIntegrable_of_Icc cut_le_half
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=cut) (b:=(1/2:ℝ))
    (fun t ht=>by
      have hmem : t∈Set.Icc cut (1/2:ℝ) := by simpa only [Set.uIcc_of_le cut_le_half] using ht
      exact cscPrimitive_hasDerivAt t (lt_of_lt_of_le cut_pos hmem.1) hmem.2) hint
  have hcutarg : Real.pi*cut/2=(1:ℝ)/254 := by unfold cut; field_simp; norm_num
  have hhalfarg : Real.pi*((1:ℝ)/2)/2=Real.pi/4 := by ring
  have htan : (1:ℝ)/254≤tan ((1:ℝ)/254) :=
    Real.le_tan (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hlog : log ((1:ℝ)/254)≤log (tan ((1:ℝ)/254)) :=
    Real.log_le_log (by norm_num) htan
  rw [heq]
  unfold cscPrimitive
  rw [hhalfarg,Real.tan_pi_div_four,Real.log_one,zero_div,hcutarg]
  have hlogInv : log ((1:ℝ)/254) = -log 254 := by simp
  rw [hlogInv] at hlog
  simp only [zero_sub]
  calc
    -(log (tan ((1:ℝ)/254))/Real.pi) ≤ -((-log 254)/Real.pi) :=
      neg_le_neg (div_le_div_of_nonneg_right hlog (le_of_lt Real.pi_pos))
    _ = log 254/Real.pi := by ring

theorem periodic_norm_bound :
    (∫ t in (0:ℝ)..1,|poly t|)≤2/Real.pi*(1+log 254) := by
  have hsmall : (∫ t in (0:ℝ)..cut,|poly t|)≤1/Real.pi := by
    calc
      _ ≤ ∫ t in (0:ℝ)..cut,(127:ℝ) :=
        intervalIntegral.integral_mono_on (le_of_lt cut_pos)
          (continuous_poly.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
          (fun t _=>poly_abs_le t)
      _ = 1/Real.pi := by simp [cut]
  have hcsc : IntervalIntegrable (fun t : ℝ=>1/sin (Real.pi*t)) volume cut (1/2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc cut_le_half
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (sin_positive_half t (lt_of_lt_of_le cut_pos ht.1) ht.2).ne'
  have hlarge : (∫ t in cut..(1/2:ℝ),|poly t|)≤log 254/Real.pi := by
    calc
      _ ≤ ∫ t in cut..(1/2:ℝ),1/sin (Real.pi*t) :=
        intervalIntegral.integral_mono_on cut_le_half
          (continuous_poly.abs.intervalIntegrable _ _) hcsc
          (fun t ht=>poly_abs_le_csc t (lt_of_lt_of_le cut_pos ht.1) ht.2)
      _ ≤ log 254/Real.pi := integral_csc_cut_half
  rw [periodic_norm_eq_twice_half]
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (continuous_poly.abs.intervalIntegrable 0 cut)
    (continuous_poly.abs.intervalIntegrable cut (1/2))]
  calc
    _ ≤ 2*(1/Real.pi+log 254/Real.pi) := by linarith
    _ = 2/Real.pi*(1+log 254) := by ring

#print axioms periodic_norm_bound
end RH080Next.AnalyticFlat64
