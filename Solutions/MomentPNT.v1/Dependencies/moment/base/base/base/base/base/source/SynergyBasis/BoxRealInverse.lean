/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyBasis.BoxRealSound

namespace SynergyBasis.RealBox
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem inv_sound {p : Nat} {a : ProofBox} {x : ℝ}
    (ha : Contains p a x) (hn : 0 < a.lo ∨ a.hi < 0) : Contains p (inv p a) x⁻¹ := by
  have hS := scale_real_pos p
  have hS0 := scale_ne_zero p
  have bounds : 1/(a.hi:ℝ) ≤ 1/(x*(scale p:ℝ)) ∧
      1/(x*(scale p:ℝ)) ≤ 1/(a.lo:ℝ) := by
    rcases hn with hp | hm
    · have hp' : (0:ℝ) < (a.lo:ℝ) := by exact_mod_cast hp
      have hx := hp'.trans_le ha.1
      exact ⟨one_div_le_one_div_of_le hx ha.2,one_div_le_one_div_of_le hp' ha.1⟩
    · have hm' : (a.hi:ℝ) < (0:ℝ) := by exact_mod_cast hm
      have hx := ha.2.trans_lt hm'
      exact ⟨one_div_le_one_div_of_neg_of_le hm' ha.2,
        one_div_le_one_div_of_neg_of_le hx ha.1⟩
  have hlo : a.lo ≠ 0 := by
    rcases hn with hp | hm
    · omega
    · have := ha.1.trans ha.2
      have hh : (a.lo:ℝ) < 0 := lt_of_le_of_lt this (by exact_mod_cast hm)
      exact_mod_cast ne_of_lt hh
  have hhi : a.hi ≠ 0 := by
    rcases hn with hp | hm
    · have := ha.1.trans ha.2
      have hh : (0:ℝ) < (a.hi:ℝ) := lt_of_lt_of_le (by exact_mod_cast hp) this
      exact_mod_cast ne_of_gt hh
    · omega
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    simp only [Contains,zero_mul] at ha
    rcases hn with hp | hm
    · have h : (0:ℝ) < (a.lo:ℝ) := by exact_mod_cast hp
      linarith [ha.1]
    · have h : (a.hi:ℝ) < (0:ℝ) := by exact_mod_cast hm
      linarith [ha.2]
  have low := mul_le_mul_of_nonneg_left bounds.1 (sq_nonneg (scale p:ℝ))
  have high := mul_le_mul_of_nonneg_left bounds.2 (sq_nonneg (scale p:ℝ))
  have he : (scale p:ℝ)^2*(1/(x*(scale p:ℝ))) = x⁻¹*(scale p:ℝ) := by
    field_simp
  rw [he] at low high
  constructor
  · have hf := floorDiv_le ((scale p)^2) a.hi hhi
    simp only [Int.cast_pow] at hf
    exact hf.trans (by simpa only [div_eq_mul_inv,one_mul] using low)
  · have hf := le_ceilDiv ((scale p)^2) a.lo hlo
    simp only [Int.cast_pow] at hf
    apply le_trans ?_ hf
    simpa only [div_eq_mul_inv,one_mul] using high

end SynergyBasis.RealBox
