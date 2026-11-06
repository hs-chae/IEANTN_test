/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Common

open Real Set MeasureTheory
namespace DirectIntervalA

/-- Each monomial in the explicit moment decays on the full real logarithmic ray.
The exponent may be negative (the fourth correction has that property). -/
theorem affine_power_exp_antitone {r m c : ℝ} (hr : (7/120 : ℝ) ≤ r)
    (hm : m ≤ 7/2) (hc : 0 ≤ c) :
    AntitoneOn (fun L : ℝ ↦ L * exp (-r*L) * (L/5+c)^m) (Ici 330) := by
  let f : ℝ → ℝ := fun L ↦ L * exp (-r*L) * (L/5+c)^m
  let d : ℝ → ℝ := fun L ↦ exp (-r*L) * (L/5+c)^m *
    (1-r*L + L*m/(5*(L/5+c)))
  have hder : ∀ L ∈ Ici (330 : ℝ), HasDerivAt f (d L) L := by
    intro L hL
    have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have hu : 0 < L/5+c := by positivity
    have hd1 := ((hasDerivAt_id L).const_mul (-r)).exp
    have hd2 := (((hasDerivAt_id L).div_const 5).add_const c).rpow_const (p:=m)
      (Or.inl hu.ne')
    have hd := ((hasDerivAt_id L).mul hd1).mul hd2
    convert hd using 1 <;> first
    | rfl
    | (simp only [id_eq, Pi.mul_apply, f, d]
       rw [Real.rpow_sub_one hu.ne' m]
       field_simp
       <;> ring)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (330 : ℝ))
    (fun L hL ↦ (hder L hL).continuousAt.continuousWithinAt)
    (fun L hL ↦ (hder L (interior_subset hL)).hasDerivWithinAt)
  intro L hL
  have hLL : (330 : ℝ) ≤ L := interior_subset hL
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hLL
  have hu : 0 < L/5+c := by positivity
  have hfrac : L*m/(5*(L/5+c)) ≤ 7/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 5*(L/5+c))).mpr
    have hmul := mul_le_mul_of_nonneg_left hm hL0.le
    nlinarith
  have hrL : (7/120 : ℝ)*330 ≤ r*L :=
    mul_le_mul hr hLL (by norm_num) (by linarith)
  have hsign : 1-r*L + L*m/(5*(L/5+c)) ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsign

end DirectIntervalA
#print axioms DirectIntervalA.affine_power_exp_antitone
