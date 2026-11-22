/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- A genuine weighted Mobius consumer, distinct from prime first-Mertens.
The exact published Abel identity remains an explicit named source boundary. -/
import MobiusSmoothing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
namespace RHContinuation.WeightedMobius
open Set MeasureTheory
open RHContinuation.MobiusSmoothing
noncomputable def m (x:ℝ) : ℝ := ∑ n∈Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n:ℝ)/n
/-- Simonic2201.10771v1, proof of Theorem2 PDFp18, the display after(51),
specialized at s=1 and using the removable reciprocal-zeta value zero. -/
def AbelAt (x:ℝ) : Prop :=
  IntegrableOn (fun u:ℝ => |M u|/u^2) (Ioi x) ∧
  |m x|≤|M x|/x+∫u in Ioi x, |M u|/u^2

theorem weighted_from_actual_M {K a x:ℝ} (hK:0≤K) (ha:a<1) (hx:1≤x)
    (hA:AbelAt x) (hM:∀u:ℝ,1≤u→|M u|≤K*u^a) :
    |m x|≤K*(1+1/(1-a))*x^(a-1) := by
  have hx0 : 0<x := by linarith
  have hint : IntegrableOn (fun u:ℝ=>K*u^(a-2)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a-2 < -1) hx0).const_mul K
  have hle : ∫u in Ioi x, |M u|/u^2 ≤ ∫u in Ioi x,K*u^(a-2) := by
    apply setIntegral_mono_on hA.1 hint measurableSet_Ioi
    intro u hu
    change x<u at hu
    have hu0 : 0<u := hx0.trans hu
    calc |M u|/u^2 ≤ (K*u^a)/u^2 := div_le_div_of_nonneg_right (hM u (by linarith [hu])) (sq_nonneg _)
      _ = K*u^(a-2) := by rw [Real.rpow_sub hu0,Real.rpow_two]; ring
  have he : ∫u in Ioi x,K*u^(a-2)=K*x^(a-1)/(1-a) := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : a-2 < -1) hx0]
    have hn : a-1≠0 := by linarith
    have he : a-2+1=a-1 := by ring
    rw [he]
    field_simp [hn,show 1-a≠0 by linarith]
    ring
  have hp : |M x|/x≤K*x^(a-1) := by
    calc _ ≤ (K*x^a)/x := div_le_div_of_nonneg_right (hM x hx) hx0.le
      _ = K*x^(a-1) := by rw [Real.rpow_sub hx0,Real.rpow_one]; ring
  have hn : 1-a≠0 := by linarith
  calc |m x|≤|M x|/x+∫u in Ioi x, |M u|/u^2 := hA.2
    _ ≤ K*x^(a-1)+K*x^(a-1)/(1-a) := by rw [←he]; linarith
    _ = K*(1+1/(1-a))*x^(a-1) := by ring

theorem weighted_power_candidate_consumer {x:ℝ} (hx:1≤x) (hA:AbelAt x)
    (hM:∀u:ℝ,1≤u→|M u|≤1100000*u^(107/132:ℝ)) :
    |m x|≤6908000*x^(-25/132:ℝ) := by
  have hh := weighted_from_actual_M (by norm_num : (0:ℝ)≤1100000)
    (by norm_num : (107/132:ℝ)<1) hx hA hM
  norm_num at hh ⊢
  exact hh
#print axioms weighted_from_actual_M
#print axioms weighted_power_candidate_consumer
end RHContinuation.WeightedMobius
