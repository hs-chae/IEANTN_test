/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyBasis.BoxRealDefs

namespace SynergyBasis.RealBox
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem scale_pos (p : Nat) : 0 < scale p := by exact pow_pos (by norm_num) p
 theorem scale_real_pos (p : Nat) : (0:ℝ) < (scale p:ℝ) := by exact_mod_cast scale_pos p
 theorem scale_ne_zero (p : Nat) : (scale p:ℝ) ≠ 0 := ne_of_gt (scale_real_pos p)

 theorem floorDiv_eq_floor_pos (n d : Int) (hd : 0 < d) :
    floorDiv n d = Int.floor ((n:ℝ)/(d:ℝ)) := by
  rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast]
  simp only [floorDiv,hd,↓reduceIte]

 theorem floorDiv_eq_floor (n d : Int) (hd : d ≠ 0) :
    floorDiv n d = Int.floor ((n:ℝ)/(d:ℝ)) := by
  by_cases h : 0 < d
  · exact floorDiv_eq_floor_pos n d h
  · have hn : 0 < -d := by omega
    have hh := floorDiv_eq_floor_pos (-n) (-d) hn
    simpa only [floorDiv,h,hn,↓reduceIte,neg_neg,Int.cast_neg,neg_div_neg_eq] using hh

 theorem ceilDiv_eq_ceil (n d : Int) (hd : d ≠ 0) :
    ceilDiv n d = Int.ceil ((n:ℝ)/(d:ℝ)) := by
  rw [ceilDiv, floorDiv_eq_floor (-n) d hd]
  simp only [Int.cast_neg,neg_div,Int.floor_neg,neg_neg]

 theorem floorDiv_le (n d : Int) (hd : d ≠ 0) :
    (floorDiv n d:ℝ) ≤ (n:ℝ)/(d:ℝ) := by
  rw [floorDiv_eq_floor n d hd]
  exact Int.floor_le _
 theorem le_ceilDiv (n d : Int) (hd : d ≠ 0) :
    (n:ℝ)/(d:ℝ) ≤ (ceilDiv n d:ℝ) := by
  rw [ceilDiv_eq_ceil n d hd]
  exact Int.le_ceil _

 theorem literal_sound (p : Nat) (n : Int) (d : Nat) (hd : 0 < d) :
    Contains p (literal p n d) ((n:ℝ)/(d:ℝ)) := by
  have hn : (d:Int) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  constructor
  · simpa only [literal,Int.cast_mul,Int.cast_natCast,div_mul_eq_mul_div] using floorDiv_le (n*scale p) (d:Int) hn
  · simpa only [literal,Int.cast_mul,Int.cast_natCast,div_mul_eq_mul_div] using le_ceilDiv (n*scale p) (d:Int) hn

 theorem add_sound {p : Nat} {a b : ProofBox} {x y : ℝ}
    (ha : Contains p a x) (hb : Contains p b y) : Contains p (add a b) (x+y) := by
  rcases ha with ⟨hl,hu⟩; rcases hb with ⟨kl,ku⟩
  constructor <;> simp only [add,Int.cast_add,add_mul] <;> linarith

 theorem neg_sound {p : Nat} {a : ProofBox} {x : ℝ}
    (ha : Contains p a x) : Contains p (neg a) (-x) := by
  rcases ha with ⟨hl,hu⟩
  constructor <;> simp only [neg,Int.cast_neg,neg_mul] <;> linarith

 theorem sub_sound {p : Nat} {a b : ProofBox} {x y : ℝ}
    (ha : Contains p a x) (hb : Contains p b y) : Contains p (sub a b) (x-y) := by
  simpa only [sub,sub_eq_add_neg] using add_sound ha (neg_sound hb)

 theorem scale_split {p q : Nat} (h : q ≤ p) :
    scale p = scale q * scale (p-q) := by
  unfold scale
  rw [← pow_add, Nat.add_sub_of_le h]

 theorem roundsFloorTo_sound {p q : Nat} {a : ProofBox} {x : ℝ} {out : Int}
    (ha : Contains p a x) (hr : roundsFloorTo p q a out = true) :
    Int.floor (x*(scale q:ℝ)) = out := by
  simp only [roundsFloorTo,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hr
  rcases hr with ⟨⟨hp,hl⟩,hu⟩
  have hd := scale_real_pos (p-q)
  have hs : (scale p:ℝ) = (scale q:ℝ)*(scale (p-q):ℝ) := by exact_mod_cast scale_split hp
  have hx : x*(scale p:ℝ)/(scale (p-q):ℝ) = x*(scale q:ℝ) := by rw [hs]; field_simp
  have hlo := div_le_div_of_nonneg_right ha.1 hd.le
  have hhi := div_le_div_of_nonneg_right ha.2 hd.le
  rw [hx] at hlo hhi
  have fl := Int.floor_mono hlo
  have fu := Int.floor_mono hhi
  rw [← floorDiv_eq_floor_pos a.lo _ (scale_pos _),hl] at fl
  rw [← floorDiv_eq_floor_pos a.hi _ (scale_pos _),hu] at fu
  exact le_antisymm fu fl

 theorem roundsCeilTo_sound {p q : Nat} {a : ProofBox} {x : ℝ} {out : Int}
    (ha : Contains p a x) (hr : roundsCeilTo p q a out = true) :
    Int.ceil (x*(scale q:ℝ)) = out := by
  simp only [roundsCeilTo,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hr
  rcases hr with ⟨⟨hp,hl⟩,hu⟩
  have hd := scale_real_pos (p-q)
  have hs : (scale p:ℝ) = (scale q:ℝ)*(scale (p-q):ℝ) := by exact_mod_cast scale_split hp
  have hx : x*(scale p:ℝ)/(scale (p-q):ℝ) = x*(scale q:ℝ) := by rw [hs]; field_simp
  have hlo := div_le_div_of_nonneg_right ha.1 hd.le
  have hhi := div_le_div_of_nonneg_right ha.2 hd.le
  rw [hx] at hlo hhi
  have fl := Int.ceil_mono hlo
  have fu := Int.ceil_mono hhi
  rw [← ceilDiv_eq_ceil a.lo _ (ne_of_gt (scale_pos _)),hl] at fl
  rw [← ceilDiv_eq_ceil a.hi _ (ne_of_gt (scale_pos _)),hu] at fu
  exact le_antisymm fu fl

 theorem roundsFloor_sound {p : Nat} {a : ProofBox} {x : ℝ} {out : Int}
    (ha : Contains p a x) (hr : roundsFloor p a out = true) :
    Int.floor (x*(scale 100:ℝ)) = out := roundsFloorTo_sound ha hr
 theorem roundsCeil_sound {p : Nat} {a : ProofBox} {x : ℝ} {out : Int}
    (ha : Contains p a x) (hr : roundsCeil p a out = true) :
    Int.ceil (x*(scale 100:ℝ)) = out := roundsCeilTo_sound ha hr

end SynergyBasis.RealBox
