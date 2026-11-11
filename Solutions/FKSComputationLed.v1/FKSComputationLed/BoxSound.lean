/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.PointSound
import FKSComputationLed.Support.RealBounds
open Real LeanCert.Core
namespace FKSComputationLed.BoxSound
open CellProgram PointProgram RealBounds

theorem cellCheck_sound (z : Input.Cell) (hab : z.a≤z.b)
    (hca : Nat.primeCounting z.a=z.ca) (hcb : Nat.primeCounting z.b=z.cb)
    (hc : cellCheck (pointInfo z.a) (pointInfo z.b) z=true) :
    ∀ x : ℝ, (z.a:ℝ)≤x → x≤(z.b:ℝ) →
      |IEANTN.primeCounting x-LiTaylor.Li2 x| ≤ (19/10:ℝ)*sqrt x/log x := by
  simp only [cellCheck,Bool.and_eq_true,and_assoc] at hc
  rcases hc with ⟨hl,hr,hu,hd⟩
  obtain ⟨ha,hla,hla',hLiA,hWA⟩ := PointSound.pointInfo_sound z.a hl
  obtain ⟨hb,hlb,hlb',hLiB,hWB⟩ := PointSound.pointInfo_sound z.b hr
  have hA : (2:ℝ)≤(z.a:ℝ) := by exact_mod_cast ha
  have hB : (2:ℝ)≤(z.b:ℝ) := by exact_mod_cast hb
  have hA0 : (0:ℝ)<(z.a:ℝ) := by linarith
  have hwA : 0≤weight (z.a:ℝ) := by unfold weight;positivity
  have hiu := IntervalDyadic.mem_mul
    (IntervalDyadic.mem_sub hLiB (PointSound.integer_mem z.ca)) hWA
  have hid := IntervalDyadic.mem_mul
    (IntervalDyadic.mem_sub (PointSound.integer_mem z.cb) hLiA) hWA
  have hU : (LiTaylor.Li2 (z.b:ℝ)-(z.ca:ℝ))*weight (z.a:ℝ)≤(19/10:ℝ) := by
    have hh := (IntervalDyadic.le_hi_of_mem hiu).trans (IntervalDyadic.upperBoundedBy_spec hu)
    simpa only [weight,Rat.cast_div,Rat.cast_ofNat] using hh
  have hD : ((z.cb:ℝ)-LiTaylor.Li2 (z.a:ℝ))*weight (z.a:ℝ)≤(19/10:ℝ) := by
    have hh := (IntervalDyadic.le_hi_of_mem hid).trans (IntervalDyadic.upperBoundedBy_spec hd)
    simpa only [weight,Rat.cast_div,Rat.cast_ofNat] using hh
  have hpA : IEANTN.primeCounting (z.a:ℝ)=(z.ca:ℝ) := by
    simpa [IEANTN.primeCounting] using congrArg (fun n:Nat=>(n:ℝ)) hca
  have hpB : IEANTN.primeCounting (z.b:ℝ)=(z.cb:ℝ) := by
    simpa [IEANTN.primeCounting] using congrArg (fun n:Nat=>(n:ℝ)) hcb
  intro x hax hxb
  have hx2 : 2≤x := hA.trans hax
  have hx0 : 0<x := hA0.trans_le hax
  have hlogx : 0<log x := log_pos (by linarith)
  have hsqrtx : 0<sqrt x := sqrt_pos.mpr hx0
  have hlixA := Li2_mono hA hax
  have hlixB := Li2_mono hx2 hxb
  have hpixA := pi_mono hax
  have hpixB := pi_mono hxb
  rw [hpA] at hpixA
  rw [hpB] at hpixB
  have hgapU : LiTaylor.Li2 x-IEANTN.primeCounting x ≤ LiTaylor.Li2 (z.b:ℝ)-(z.ca:ℝ) := by linarith
  have hgapD : -(LiTaylor.Li2 x-IEANTN.primeCounting x) ≤ (z.cb:ℝ)-LiTaylor.Li2 (z.a:ℝ) := by linarith
  have hmu := (mul_le_mul_of_nonneg_right hgapU hwA).trans hU
  have hmd := (mul_le_mul_of_nonneg_right hgapD hwA).trans hD
  have habs : |LiTaylor.Li2 x-IEANTN.primeCounting x| *weight (z.a:ℝ)≤(19/10:ℝ) := by
    have hh : |(LiTaylor.Li2 x-IEANTN.primeCounting x)*weight (z.a:ℝ)|≤(19/10:ℝ) :=
      abs_le.mpr ⟨by nlinarith,hmu⟩
    simpa only [abs_mul,abs_of_nonneg hwA] using hh
  have hxw := weight_antitone hA0 hla hax
  have hfinal := (mul_le_mul_of_nonneg_left hxw
    (abs_nonneg (LiTaylor.Li2 x-IEANTN.primeCounting x))).trans habs
  have hwx : 0<weight x := div_pos hlogx hsqrtx
  have hh : |IEANTN.primeCounting x-LiTaylor.Li2 x| ≤ (19/10:ℝ)/weight x := by
    apply (le_div_iff₀ hwx).mpr
    simpa only [abs_sub_comm] using hfinal
  calc
    _ ≤ (19/10:ℝ)/weight x := hh
    _ = _ := by unfold weight;field_simp
#print axioms cellCheck_sound
end FKSComputationLed.BoxSound
