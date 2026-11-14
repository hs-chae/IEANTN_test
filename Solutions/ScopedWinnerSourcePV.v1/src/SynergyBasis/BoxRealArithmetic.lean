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

private theorem product_bounds {l h m n x y L H : ℝ}
    (hx : l ≤ x ∧ x ≤ h) (hy : m ≤ y ∧ y ≤ n)
    (h00 : L ≤ l*m) (h01 : L ≤ l*n) (h10 : L ≤ h*m) (h11 : L ≤ h*n)
    (k00 : l*m ≤ H) (k01 : l*n ≤ H) (k10 : h*m ≤ H) (k11 : h*n ≤ H) :
    L ≤ x*y ∧ x*y ≤ H := by
  by_cases hp : 0 ≤ x
  · constructor
    · have low := mul_le_mul_of_nonneg_left hy.1 hp
      by_cases hm : 0 ≤ m
      · exact h00.trans ((mul_le_mul_of_nonneg_right hx.1 hm).trans low)
      · exact h10.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hm)).trans low)
    · have high := mul_le_mul_of_nonneg_left hy.2 hp
      by_cases hn : 0 ≤ n
      · exact high.trans ((mul_le_mul_of_nonneg_right hx.2 hn).trans k11)
      · exact high.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hn)).trans k01)
  · have hp' : x ≤ 0 := le_of_not_ge hp
    constructor
    · have low := mul_le_mul_of_nonpos_left hy.2 hp'
      by_cases hn : 0 ≤ n
      · exact h01.trans ((mul_le_mul_of_nonneg_right hx.1 hn).trans low)
      · exact h11.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hn)).trans low)
    · have high := mul_le_mul_of_nonpos_left hy.1 hp'
      by_cases hm : 0 ≤ m
      · exact high.trans ((mul_le_mul_of_nonneg_right hx.2 hm).trans k10)
      · exact high.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hm)).trans k00)

private theorem min4_le_all (a b c d : Int) :
    min4 a b c d ≤ a ∧ min4 a b c d ≤ b ∧ min4 a b c d ≤ c ∧ min4 a b c d ≤ d := by
  unfold min4
  exact ⟨(min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩
private theorem all_le_max4 (a b c d : Int) :
    a ≤ max4 a b c d ∧ b ≤ max4 a b c d ∧ c ≤ max4 a b c d ∧ d ≤ max4 a b c d := by
  unfold max4
  exact ⟨(le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

 theorem mul_sound {p : Nat} {a b : ProofBox} {x y : ℝ}
    (ha : Contains p a x) (hb : Contains p b y) : Contains p (mul p a b) (x*y) := by
  let low := min4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  let high := max4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  have hl := min4_le_all (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  have hu := all_le_max4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)
  have l00 : (low:ℝ) ≤ (a.lo:ℝ)*(b.lo:ℝ) := by exact_mod_cast hl.1
  have l01 : (low:ℝ) ≤ (a.lo:ℝ)*(b.hi:ℝ) := by exact_mod_cast hl.2.1
  have l10 : (low:ℝ) ≤ (a.hi:ℝ)*(b.lo:ℝ) := by exact_mod_cast hl.2.2.1
  have l11 : (low:ℝ) ≤ (a.hi:ℝ)*(b.hi:ℝ) := by exact_mod_cast hl.2.2.2
  have u00 : (a.lo:ℝ)*(b.lo:ℝ) ≤ (high:ℝ) := by exact_mod_cast hu.1
  have u01 : (a.lo:ℝ)*(b.hi:ℝ) ≤ (high:ℝ) := by exact_mod_cast hu.2.1
  have u10 : (a.hi:ℝ)*(b.lo:ℝ) ≤ (high:ℝ) := by exact_mod_cast hu.2.2.1
  have u11 : (a.hi:ℝ)*(b.hi:ℝ) ≤ (high:ℝ) := by exact_mod_cast hu.2.2.2
  have h := product_bounds ha hb l00 l01 l10 l11 u00 u01 u10 u11
  have hp := scale_real_pos p
  have hn := ne_of_gt (scale_pos p)
  have hlow := div_le_div_of_nonneg_right h.1 hp.le
  have hhigh := div_le_div_of_nonneg_right h.2 hp.le
  have hs : ((x*(scale p:ℝ))*(y*(scale p:ℝ)))/(scale p:ℝ) = (x*y)*(scale p:ℝ) := by
    field_simp
  rw [hs] at hlow hhigh
  constructor
  · exact (floorDiv_le low (scale p) hn).trans hlow
  · exact hhigh.trans (le_ceilDiv high (scale p) hn)

 theorem pow_sound {p : Nat} {a : ProofBox} {x : ℝ}
    (ha : Contains p a x) (n : Nat) : Contains p (pow p a n) (x^n) := by
  induction n with
  | zero => simpa only [pow,pow_zero,Int.cast_one,Nat.cast_one,div_one] using literal_sound p 1 1 (by omega)
  | succ n ih => simpa only [pow,pow_succ,mul_comm] using mul_sound ha ih

end SynergyBasis.RealBox
