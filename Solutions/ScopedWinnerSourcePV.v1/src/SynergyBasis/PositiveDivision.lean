/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyBasis.PositiveModel
namespace SynergyBasis.Positive
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis.RealBox
set_option autoImplicit false
set_option maxHeartbeats 0

def divI (a b : ProofBox) : ProofBox :=
  ⟨floorDiv (a.lo*scale p) b.hi,ceilDiv (a.hi*scale p) b.lo⟩

theorem divI_sound {a b : ProofBox} {x y : ℝ}
    (ha : RealBox.Contains p a x) (hb : RealBox.Contains p b y)
    (hx : 0 ≤ x) (hbl : 0 < b.lo) :
    RealBox.Contains p (divI a b) (x/y) := by
  have hs := RealBox.scale_real_pos p
  have hl : (0:ℝ) < (b.lo:ℝ) := by exact_mod_cast hbl
  have hy : 0 < y := by nlinarith [hb.1]
  have hh : (0:ℝ) < (b.hi:ℝ) := (mul_pos hy hs).trans_le hb.2
  have hn : b.hi ≠ 0 := by exact_mod_cast ne_of_gt hh
  have hm : b.lo ≠ 0 := ne_of_gt hbl
  have hq : 0 ≤ x/y := div_nonneg hx hy.le
  have lower : ((a.lo:ℝ)*(scale p:ℝ))/(b.hi:ℝ) ≤ (x/y)*(scale p:ℝ) := by
    apply (div_le_iff₀ hh).2
    calc
      (a.lo:ℝ)*(scale p:ℝ) ≤ (x*(scale p:ℝ))*(scale p:ℝ) := mul_le_mul_of_nonneg_right ha.1 hs.le
      _ = (x/y)*(y*(scale p:ℝ))*(scale p:ℝ) := by field_simp
      _ ≤ (x/y)*(b.hi:ℝ)*(scale p:ℝ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2 hq) hs.le
      _ = (x/y)*(scale p:ℝ)*(b.hi:ℝ) := by ring
  have upper : (x/y)*(scale p:ℝ) ≤ ((a.hi:ℝ)*(scale p:ℝ))/(b.lo:ℝ) := by
    apply (le_div_iff₀ hl).2
    calc
      (x/y)*(scale p:ℝ)*(b.lo:ℝ) = (x/y)*(b.lo:ℝ)*(scale p:ℝ) := by ring
      _ ≤ (x/y)*(y*(scale p:ℝ))*(scale p:ℝ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.1 hq) hs.le
      _ = (x*(scale p:ℝ))*(scale p:ℝ) := by field_simp
      _ ≤ (a.hi:ℝ)*(scale p:ℝ) := mul_le_mul_of_nonneg_right ha.2 hs.le
  constructor
  · change (floorDiv (a.lo*scale p) b.hi:ℝ) ≤ (x/y)*(scale p:ℝ)
    have hf := RealBox.floorDiv_le (a.lo*scale p) b.hi hn
    simp only [Int.cast_mul] at hf
    exact hf.trans lower
  · change (x/y)*(scale p:ℝ) ≤ (ceilDiv (a.hi*scale p) b.lo:ℝ)
    have hf := RealBox.le_ceilDiv (a.hi*scale p) b.lo hm
    simp only [Int.cast_mul] at hf
    exact upper.trans hf

theorem positiveSub_endpoints (a b : ProofBox) :
    positiveSub a b = ⟨Max.max 0 (a.lo-b.hi),Max.max 0 (a.hi-b.lo)⟩ := by
  simp [positiveSub,ProofBox.max,zero,sub,add,neg,sub_eq_add_neg]

theorem positive_mul_endpoints {a b : ProofBox}
    (ha0 : 0 ≤ a.lo) (ha : a.lo ≤ a.hi) (hb0 : 0 ≤ b.lo) (hb : b.lo ≤ b.hi) :
    mul p a b = ⟨floorDiv (a.lo*b.lo) (scale p),ceilDiv (a.hi*b.hi) (scale p)⟩ := by
  have hA : 0 ≤ a.hi := ha0.trans ha
  have hB : 0 ≤ b.hi := hb0.trans hb
  have h01 := mul_le_mul_of_nonneg_left hb ha0
  have h10 := mul_le_mul_of_nonneg_right ha hb0
  have h11 := mul_le_mul ha hb hb0 hA
  have k01 := mul_le_mul_of_nonneg_right ha hB
  have k10 := mul_le_mul_of_nonneg_left hb hA
  have hm : min4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) = a.lo*b.lo := by
    simp only [min4,min_eq_left h01,min_eq_left (mul_le_mul_of_nonneg_left hb hA)]
    exact min_eq_left h10
  have hx : max4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) = a.hi*b.hi := by
    simp only [max4,max_eq_right h01,max_eq_right (mul_le_mul_of_nonneg_left hb hA)]
    exact max_eq_right k01
  simp only [mul,hm,hx]

#print axioms divI_sound
#print axioms positive_mul_endpoints
end SynergyBasis.Positive
