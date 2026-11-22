/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
namespace RHContinuation.MobiusSmoothing
open Finset ArithmeticFunction
noncomputable def M (x:ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n:ℝ)
noncomputable def smoothedM (x:ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (x-n)*(ArithmeticFunction.moebius n:ℝ)
noncomputable def newTerms (x h:ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, (x+h-n)*(ArithmeticFunction.moebius n:ℝ)

theorem smoothing_identity {x h:ℝ} (hh:0≤h) :
    smoothedM (x+h)-smoothedM x-h*M x=newTerms x h := by
  have hle : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have heq : Finset.Ioc 0 ⌊x+h⌋₊ = Finset.Ioc 0 ⌊x⌋₊ ∪
      Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by ext n; simp only [Finset.mem_Ioc,Finset.mem_union]; omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have h1 := (Finset.mem_Ioc.mp hn).2
    have h2 := (Finset.mem_Ioc.mp hn').1
    omega
  unfold smoothedM
  rw [heq,Finset.sum_union hd]
  unfold M newTerms
  rw [Finset.mul_sum]
  have hsum : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,(x+h-n)*(ArithmeticFunction.moebius n:ℝ))-
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,(x-n)*(ArithmeticFunction.moebius n:ℝ))-
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,h*(ArithmeticFunction.moebius n:ℝ))=0 := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro n hn
    ring
  linarith

theorem moebius_abs_le_one (n:ℕ) : |(ArithmeticFunction.moebius n:ℝ)|≤1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=n))

theorem newTerms_bound {x h:ℝ} (hx:0≤x) (hh:0≤h) : |newTerms x h|≤h*(h+1) := by
  let s := Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊
  have hpoint : ∀ n∈s, |(x+h-n)*(ArithmeticFunction.moebius n:ℝ)|≤h := by
    intro n hn
    have hI := Finset.mem_Ioc.mp hn
    have hnx : x<(n:ℝ) := Nat.lt_of_floor_lt hI.1
    have hnhi : (n:ℝ)≤x+h := (Nat.cast_le.mpr hI.2).trans (Nat.floor_le (by linarith))
    have hw0 : 0≤x+h-n := by linarith
    have hwh : x+h-n≤h := by linarith
    rw [abs_mul,abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_left (moebius_abs_le_one n) hw0).trans (by linarith)
  have hc : (s.card:ℝ)≤h+1 := by
    have hle : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
    have hlo := Nat.lt_floor_add_one x
    have hhi := Nat.floor_le (show 0≤x+h by linarith)
    dsimp [s]
    rw [Nat.card_Ioc,Nat.cast_sub hle]
    linarith
  have hs : |newTerms x h|≤s.card*h := by
    unfold newTerms
    calc _ ≤ ∑ n∈s, |(x+h-n)*(ArithmeticFunction.moebius n:ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n∈s,h := Finset.sum_le_sum hpoint
      _ = _ := by simp
  exact hs.trans (by nlinarith)

/-- The ordinary floor endpoints are proved for the actual Mobius sum.
No RH or source theorem is needed for this finite smoothing step. -/
theorem smoothing_discrepancy {x h:ℝ} (hx:0≤x) (hh:0<h) :
    |(smoothedM (x+h)-smoothedM x)/h-M x|≤h+1 := by
  have hi := smoothing_identity (x:=x) hh.le
  have hb := newTerms_bound hx hh.le
  have he : (smoothedM (x+h)-smoothedM x)/h-M x=newTerms x h/h := by
    field_simp [ne_of_gt hh]
    nlinarith
  rw [he,abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr (by nlinarith)

#print axioms smoothing_discrepancy
end RHContinuation.MobiusSmoothing
