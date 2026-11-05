/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.DirectRHResult
namespace ScopedWinnerA.Comparison
open Real IEANTN
set_option maxHeartbeats 0
noncomputable def oldExact : ℝ := (1+1/1000000000)*(9474448/1000000000)+
  1/1000000000000+1/100000000
noncomputable def newCap : ℝ := 947147/100000000
noncomputable def scale (x : ℝ) : ℝ := x^(-(1:ℝ)/8)
def domain (x : ℝ) : Prop := exp 330≤x ∧ x≤exp 331

theorem logs {x : ℝ} (hx : domain x) : 330≤log x ∧ log x≤331 := by
  have hp : 0<x := (exp_pos _).trans_le hx.1
  exact ⟨by simpa only [log_exp] using log_le_log (exp_pos _) hx.1,
    by simpa only [log_exp] using log_le_log hp hx.2⟩
theorem scale_eq {x : ℝ} (hx : domain x) : scale x=exp (-(log x)/8) := by
  rw [scale,rpow_def_of_pos ((exp_pos _).trans_le hx.1)]
  congr 1
  ring

theorem standard_curve {x A B C R : ℝ} (hx : domain x)
    (hA : (1/100:ℝ)≤A) (hB : 0≤B) (hC : 0≤C) (hC' : C≤2)
    (hR : 1≤R) (hR' : R≤6) :
    (473723/50000000:ℝ)*scale x < admissibleBound A B C R x := by
  obtain ⟨hL,hL'⟩:=logs hx
  have hR0 : 0<R := by linarith
  have hu : 1≤log x/R := (le_div_iff₀ hR0).2 (by nlinarith)
  have hu0 : 0≤log x/R := by linarith
  have hu1 : log x/R≤331 := (div_le_iff₀ hR0).2 (by nlinarith)
  have hs0 : 0≤(log x/R)^((1:ℝ)/2) := rpow_nonneg hu0 _
  have hs : (log x/R)^((1:ℝ)/2)≤19 := by
    rw [←sqrt_eq_rpow]
    exact (sqrt_le_iff).2 ⟨by norm_num,by nlinarith⟩
  have hp : 1≤(log x/R)^B := one_le_rpow hu hB
  have he : -log x/8≤-C*(log x/R)^((1:ℝ)/2) := by nlinarith
  rw [scale_eq hx]
  unfold admissibleBound
  calc
    _ < A*exp (-log x/8) := mul_lt_mul_of_pos_right (by linarith) (exp_pos _)
    _ ≤ A*(log x/R)^B*exp (-C*(log x/R)^((1:ℝ)/2)) := by
      apply mul_le_mul
      · nlinarith
      · exact exp_le_exp.mpr he
      · exact (exp_pos _).le
      · positivity

theorem classical3 {x : ℝ} (hx : domain x) :
    (473723/50000000:ℝ)*scale x < admissibleBound (3/100000000) 2 2 1 x := by
  obtain ⟨hL,hL'⟩:=logs hx
  have hL0 : 0≤log x := by linarith
  have hs : (log x)^((1:ℝ)/2)≤19 := by
    rw [←sqrt_eq_rpow]
    exact (sqrt_le_iff).2 ⟨by norm_num,by nlinarith⟩
  have hs0 : 0≤(log x)^((1:ℝ)/2) := rpow_nonneg hL0 _
  have he : 3≤log x/8-2*(log x)^((1:ℝ)/2) := by nlinarith
  have hExp : 4≤exp (log x/8-2*(log x)^((1:ℝ)/2)) :=
    (by linarith : (4:ℝ)≤(log x/8-2*(log x)^((1:ℝ)/2))+1).trans (add_one_le_exp _)
  have hsq : (330:ℝ)^2≤(log x)^2 := by nlinarith
  have hcoef : (473723/50000000:ℝ)<(3/100000000)*(log x)^2*
      exp (log x/8-2*(log x)^((1:ℝ)/2)) := by nlinarith
  rw [scale_eq hx]
  unfold admissibleBound
  simp only [div_one,rpow_two]
  have hm:=mul_lt_mul_of_pos_right hcoef (exp_pos (-log x/8))
  have hid : exp (log x/8-2*(log x)^((1:ℝ)/2))*exp (-log x/8)=
      exp (-2*(log x)^((1:ℝ)/2)) := by
    rw [←exp_add]
    congr 1
    ring
  simpa only [mul_assoc,hid] using hm

theorem numeric_tiny {x : ℝ} (hx : domain x) :
    (473723/50000000:ℝ)*scale x < (5:ℝ)/10^16 := by
  have he:= (CH2Section7A.exp_nat_bounds 40).1
  have hL:=(logs hx).1
  have hex : exp (40:ℝ)≤exp (log x/8) := exp_le_exp.mpr (by linarith)
  have hlarge : (10:ℝ)^17≤exp (log x/8) := by norm_num at he;linarith
  have hh : (473723/50000000:ℝ)<((5:ℝ)/10^16)*exp (log x/8) := by nlinarith
  rw [scale_eq hx,show -log x/8=-(log x/8) by ring,exp_neg]
  rw [←div_eq_mul_inv]
  exact (div_lt_iff₀ (exp_pos _)).2 hh

theorem power_floor {x c : ℝ} (hx : domain x) (hc : (473723/50000000:ℝ)≤c) :
    (oldExact*scale x)≤c*scale x := by
  apply mul_le_mul_of_nonneg_right _ (rpow_nonneg ((exp_pos _).trans_le hx.1).le _)
  exact (by norm_num [oldExact] : oldExact≤(473723/50000000:ℝ)).trans hc

theorem strict_increment {x : ℝ} (hx : domain x) :
    newCap*scale x+(298/100000000:ℝ)*scale x < oldExact*scale x := by
  rw [←add_mul]
  apply mul_lt_mul_of_pos_right _ (rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _)
  norm_num [newCap,oldExact]
#print axioms standard_curve
#print axioms classical3
#print axioms numeric_tiny
#print axioms strict_increment
end ScopedWinnerA.Comparison

namespace ScopedWinnerA.Comparison
open Real IEANTN
set_option maxHeartbeats 0

theorem log2_power {x C β : ℝ} (hx : domain x)
    (hC : (1/10000:ℝ)≤C) (hβ : (7/8:ℝ)≤β) :
    (473723/50000000:ℝ)*scale x < C*(log x)^2*x^(β-1) := by
  have hL := (logs hx).1
  have hx1 : 1≤x := (by linarith [add_one_le_exp (330:ℝ)] : (1:ℝ)≤exp 330).trans hx.1
  have hs : scale x≤x^(β-1) := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : (330:ℝ)^2≤(log x)^2 := by nlinarith
  have hcoef : (473723/50000000:ℝ)<C*(log x)^2 := by nlinarith
  have hp : 0<scale x := rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _
  exact (mul_lt_mul_of_pos_right hcoef hp).trans_le
    (mul_le_mul_of_nonneg_left hs (by positivity))
end ScopedWinnerA.Comparison
