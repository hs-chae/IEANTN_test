/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.BaselineSound
namespace FKSComputationLed.BaselineTransfer
open Real Finset BaselineSound RealBounds
noncomputable def correction (x : ℝ) : ℝ :=
  ∑ k∈range 29, IEANTN.primeCounting (x^((1:ℝ)/(k+2:ℕ)))/(k+2:ℕ)
noncomputable def fullStarLower (x : ℝ) : ℝ := 1+(correction x-2)*weight x

lemma counting_nonneg (x : ℝ) : 0≤IEANTN.primeCounting x := by
  unfold IEANTN.primeCounting
  positivity

lemma correction_ge_square (x : ℝ) :
    IEANTN.primeCounting (sqrt x)/2≤correction x := by
  have hh := single_le_sum (f:=fun k:Nat=>
    IEANTN.primeCounting (x^((1:ℝ)/(k+2:ℕ)))/(k+2:ℕ))
    (fun k _=>div_nonneg (counting_nonneg _) (by positivity)) (by simp : (0:Nat)∈range 29)
  rw [sqrt_eq_rpow]
  simpa [correction] using hh

lemma primeCounting_zero_lt_two {y : ℝ} (hy0 : 0≤y) (hy : y<2) : IEANTN.primeCounting y=0 := by
  have hn : ⌊y⌋₊<2 := (Nat.floor_lt hy0).mpr hy
  have hc : Nat.primeCounting ⌊y⌋₊=0 := Nat.primeCounting_eq_zero_iff.mpr (by omega)
  simp only [IEANTN.primeCounting,hc,Nat.cast_zero]

lemma high_terms_zero (x : ℝ) (hx : 0<x) (hxU : x≤1000000000)
    (k : Nat) (hk : 30≤k) :
    IEANTN.primeCounting (x^((1:ℝ)/(k+1:ℕ)))/(k+1:ℕ)=0 := by
  have hxP : x<(2:ℝ)^30 := by norm_num;linarith
  have hlog : log x<30*log 2 := by
    have hh := log_lt_log hx hxP
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hlog2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hk1 : (30:ℝ)≤((k+1:Nat):ℝ) := by exact_mod_cast (by omega : 30≤k+1)
  have hk0 : (0:ℝ)<((k+1:Nat):ℝ) := by positivity
  have hr : x^((1:ℝ)/(k+1:ℕ))<2 := by
    rw [rpow_def_of_pos hx,←exp_log (by norm_num : (0:ℝ)<2)]
    apply exp_lt_exp.mpr
    have hd : log x/((k+1:Nat):ℝ)<log 2 := (div_lt_iff₀ hk0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv,one_mul] using hd
  rw [primeCounting_zero_lt_two (rpow_nonneg hx.le _) hr]
  simp

/-- Exact finite cutoff for the actual IEANTN Riemann counting definition on this window. -/
theorem riemann_decomposition (x : ℝ) (hx : 0<x) (hxU : x≤1000000000) :
    IEANTN.riemannPrimeCounting x=IEANTN.primeCounting x+correction x := by
  unfold IEANTN.riemannPrimeCounting
  rw [tsum_eq_sum (s:=range 30) (fun k hk=>by
    simpa only [Nat.cast_add,Nat.cast_one] using high_terms_zero x hx hxU k (by simpa using hk))]
  rw [sum_range_succ']
  simp only [Nat.cast_zero,zero_add,div_one,rpow_one]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro k hk
  congr 2 <;> push_cast <;> ring

theorem full_old_profiles_comparison (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (19/10:ℝ)≤(9/10)*min (fullStarLower x) (directLower x) := by
  have hlog0 : 0<log x := log_pos (by linarith)
  have hw : 0≤weight x := div_nonneg hlog0.le (sqrt_nonneg _)
  have hs : squareLower x≤fullStarLower x := by
    unfold squareLower fullStarLower
    have hh := mul_le_mul_of_nonneg_right (sub_le_sub_right (correction_ge_square x) 2) hw
    linarith
  have hh := both_comparison x hx hxU
  have hm := min_le_min hs (le_refl (directLower x))
  exact hh.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

#print axioms riemann_decomposition
#print axioms full_old_profiles_comparison
end FKSComputationLed.BaselineTransfer
