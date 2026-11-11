/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import Mathlib
import IEANTN.Vocabulary.PrimeCounting
import FKSComputationLed.Support.LiTaylor
namespace FKSComputationLed.RealBounds
open Real Finset MeasureTheory intervalIntegral
theorem poly_exp_decreasing (n : ℕ) {c L0 L : ℝ} (hL0 : 0 < L0) (hc : (n : ℝ) / L0 ≤ c)
    (hL : L0 ≤ L) : L ^ n * Real.exp (-c * L) ≤ L0 ^ n * Real.exp (-c * L0) := by
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hratio_pos : (0 : ℝ) < L / L0 := div_pos hLpos hL0
  have hlog_ratio : Real.log (L / L0) ≤ L / L0 - 1 := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_sub : Real.log L - Real.log L0 ≤ (L - L0) / L0 := by
    have heq : Real.log (L / L0) = Real.log L - Real.log L0 :=
      Real.log_div (ne_of_gt hLpos) (ne_of_gt hL0)
    have heq2 : L / L0 - 1 = (L - L0) / L0 := by field_simp
    linarith [hlog_ratio, heq, heq2]
  have hkey : (n : ℝ) * (Real.log L - Real.log L0) ≤ c * (L - L0) := by
    have hLsub_nonneg : (0 : ℝ) ≤ L - L0 := by linarith
    have hstep1 : (n : ℝ) * (Real.log L - Real.log L0) ≤ (n : ℝ) * ((L - L0) / L0) :=
      mul_le_mul_of_nonneg_left hlog_sub (Nat.cast_nonneg n)
    have hstep2 : (n : ℝ) * ((L - L0) / L0) ≤ c * (L - L0) := by
      have hmm := mul_le_mul_of_nonneg_right hc hLsub_nonneg
      calc (n : ℝ) * ((L - L0) / L0) = ((n : ℝ) / L0) * (L - L0) := by ring
        _ ≤ c * (L - L0) := hmm
    linarith
  have hrw : ∀ v : ℝ, 0 < v →
      Real.exp ((n : ℝ) * Real.log v - c * v) = v ^ n * Real.exp (-c * v) := by
    intro v hvpos
    have hsplit : (n : ℝ) * Real.log v - c * v = ((n : ℝ) * Real.log v) + (-c * v) := by ring
    rw [hsplit, Real.exp_add]
    congr 1
    rw [show (n : ℝ) * Real.log v = Real.log (v ^ n) from (Real.log_pow v n).symm]
    exact Real.exp_log (by positivity)
  have hexp_le : Real.exp ((n : ℝ) * Real.log L - c * L)
      ≤ Real.exp ((n : ℝ) * Real.log L0 - c * L0) := by
    apply Real.exp_le_exp.mpr; linarith [hkey]
  rw [hrw L hLpos, hrw L0 hL0] at hexp_le
  exact hexp_le


noncomputable def weight (x : ℝ) : ℝ := log x/sqrt x
lemma weight_eq {x : ℝ} (hx : 0<x) : weight x = log x*exp (-log x/2) := by
  unfold weight
  rw [sqrt_eq_rpow,rpow_def_of_pos hx,div_eq_mul_inv,←exp_neg]
  congr 1
  ring
lemma weight_antitone {a x : ℝ} (ha : 0<a) (hlog : 2≤log a) (hax : a≤x) :
    weight x ≤ weight a := by
  have hx : 0<x := ha.trans_le hax
  have hla : 0<log a := by linarith
  have hl := log_le_log ha hax
  have hh := poly_exp_decreasing 1 (L0:=log a) (c:=(1/2:ℝ)) hla
    ((div_le_iff₀ hla).mpr (by norm_num;linarith)) hl
  rw [weight_eq ha,weight_eq hx]
  simpa only [pow_one,show ∀t:ℝ,-(1/2:ℝ)*t = -t/2 by intro;ring] using hh
lemma pi_mono {a b : ℝ} (hab : a≤b) : IEANTN.primeCounting a ≤ IEANTN.primeCounting b := by
  unfold IEANTN.primeCounting
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hab)
lemma Li2_mono {a b : ℝ} (ha : 2≤a) (hab : a≤b) : LiTaylor.Li2 a ≤ LiTaylor.Li2 b := by
  have hcont (x : ℝ) (hx : 2≤x) :
      ContinuousOn (fun t : ℝ=>1/log t) (Set.uIcc (2:ℝ) x) := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1<t := by linarith [ht.1]
    exact (continuousAt_const.div (continuousAt_log (by linarith))
      (log_pos ht1).ne').continuousWithinAt
  have hiA : IntervalIntegrable (fun t : ℝ=>1/log t) volume 2 a := (hcont a ha).intervalIntegrable
  have hiB : IntervalIntegrable (fun t : ℝ=>1/log t) volume 2 b := (hcont b (ha.trans hab)).intervalIntegrable
  have hs := integral_interval_sub_left hiB hiA
  have hn : 0≤∫ t in a..b, (1:ℝ)/log t := by
    apply integral_nonneg hab
    intro t ht
    have ht1 : 1<t := by linarith [ht.1]
    exact div_nonneg zero_le_one (log_pos ht1).le
  unfold LiTaylor.Li2
  linarith
#print axioms weight_antitone
#print axioms pi_mono
#print axioms Li2_mono
end FKSComputationLed.RealBounds
