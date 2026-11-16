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

 theorem min_sound {p : Nat} {a b : ProofBox} {x y : ℝ}
    (ha : Contains p a x) (hb : Contains p b y) :
    Contains p (min a b) (Min.min x y) := by
  constructor
  · change ((Min.min a.lo b.lo:Int):ℝ) ≤ Min.min x y * (scale p:ℝ)
    rw [Int.cast_min,min_mul_of_nonneg x y (scale_real_pos p).le]
    exact min_le_min ha.1 hb.1
  · change Min.min x y * (scale p:ℝ) ≤ ((Min.min a.hi b.hi:Int):ℝ)
    rw [Int.cast_min,min_mul_of_nonneg x y (scale_real_pos p).le]
    exact min_le_min ha.2 hb.2

 theorem max_sound {p : Nat} {a b : ProofBox} {x y : ℝ}
    (ha : Contains p a x) (hb : Contains p b y) :
    Contains p (max a b) (Max.max x y) := by
  constructor
  · change ((Max.max a.lo b.lo:Int):ℝ) ≤ Max.max x y * (scale p:ℝ)
    rw [Int.cast_max,max_mul_of_nonneg x y (scale_real_pos p).le]
    exact max_le_max ha.1 hb.1
  · change Max.max x y * (scale p:ℝ) ≤ ((Max.max a.hi b.hi:Int):ℝ)
    rw [Int.cast_max,max_mul_of_nonneg x y (scale_real_pos p).le]
    exact max_le_max ha.2 hb.2

 theorem abs_sound {p : Nat} {a : ProofBox} {x : ℝ}
    (ha : Contains p a x) : Contains p (ScopedNumerical.ProofBox.abs a) |x| := by
  have hs := scale_real_pos p
  by_cases hl : 0 ≤ a.lo
  · have hl' : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast hl
    have hx : 0 ≤ x := nonneg_of_mul_nonneg_left (hl'.trans ha.1) hs
    simpa only [ScopedNumerical.ProofBox.abs,hl,↓reduceIte,abs_of_nonneg hx] using ha
  · by_cases hh : a.hi ≤ 0
    · have hh' : (a.hi:ℝ) ≤ (0:ℝ) := by exact_mod_cast hh
      have hx : x ≤ 0 := nonpos_of_mul_nonpos_left (ha.2.trans hh') hs
      simpa only [ScopedNumerical.ProofBox.abs,hl,hh,↓reduceIte,abs_of_nonpos hx] using neg_sound ha
    · rw [ScopedNumerical.ProofBox.abs,if_neg hl,if_neg hh]
      change Contains p ⟨0,Max.max (-a.lo) a.hi⟩ |x|
      constructor
      · simpa only [Int.cast_zero] using mul_nonneg (abs_nonneg x) hs.le
      · change |x| *(scale p:ℝ) ≤ ((Max.max (-a.lo) a.hi:Int):ℝ)
        rw [Int.cast_max,Int.cast_neg,← abs_of_pos hs,← abs_mul]
        apply abs_le.mpr
        have h0 : -(a.lo:ℝ) ≤ Max.max (-(a.lo:ℝ)) (a.hi:ℝ) := le_max_left _ _
        have h1 : (a.hi:ℝ) ≤ Max.max (-(a.lo:ℝ)) (a.hi:ℝ) := le_max_right _ _
        constructor <;> linarith [ha.1,ha.2]

end SynergyBasis.RealBox
