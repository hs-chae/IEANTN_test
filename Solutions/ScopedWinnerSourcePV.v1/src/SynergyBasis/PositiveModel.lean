/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyBasis.BoxRealArithmetic
import SynergyBasis.BoxRealLattice
import SynergyAnalytic.HornerRange

namespace SynergyBasis.Positive
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis.RealBox
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Mathematical directed-arithmetic model. Source statement execution and
512-bit range applicability are separate obligations; this is not a PV claim. -/
def p : Nat := 128
def one : ProofBox := ⟨scale p,scale p⟩
def zero : ProofBox := ⟨0,0⟩
def divN (a : ProofBox) (n : Nat) : ProofBox :=
  ⟨floorDiv a.lo n,ceilDiv a.hi n⟩
def positiveSub (a b : ProofBox) : ProofBox :=
  ProofBox.max zero (sub a b)
def horner (z : ProofBox) : Nat → Nat → ProofBox
  | 0, _ => one
  | n+1,k => positiveSub one (divN (mul p z (horner z n (k+1))) (k+1))
def widen (a : ProofBox) : ProofBox := ⟨Max.max 0 (a.lo-1),a.hi+1⟩
def squares : Nat → ProofBox → ProofBox
  | 0,a => a
  | n+1,a => squares n (mul p a a)
def expNeg (x : ProofBox) : ProofBox :=
  squares 6 (widen (horner (divN x 64) 48 0))

theorem one_sound : RealBox.Contains p one 1 := by simp [RealBox.Contains,one]
theorem zero_sound : RealBox.Contains p zero 0 := by simp [RealBox.Contains,zero]

theorem divN_sound {a : ProofBox} {x : ℝ} {n : Nat}
    (ha : RealBox.Contains p a x) (hn : 0 < n) : RealBox.Contains p (divN a n) (x/n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnI : (n:Int) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hl := (RealBox.floorDiv_le a.lo (n:Int) hnI).trans
    (div_le_div_of_nonneg_right ha.1 hnR.le)
  have hu := (div_le_div_of_nonneg_right ha.2 hnR.le).trans
    (RealBox.le_ceilDiv a.hi (n:Int) hnI)
  constructor
  · simpa only [divN,Int.cast_natCast,div_mul_eq_mul_div] using hl
  · simpa only [divN,Int.cast_natCast,div_mul_eq_mul_div] using hu

theorem positiveSub_sound {a b : ProofBox} {x y : ℝ}
    (ha : RealBox.Contains p a x) (hb : RealBox.Contains p b y) :
    RealBox.Contains p (positiveSub a b) (Max.max 0 (x-y)) :=
  RealBox.max_sound zero_sound (RealBox.sub_sound ha hb)

theorem horner_sound {z : ProofBox} {x : ℝ}
    (hz : RealBox.Contains p z x) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n k : Nat) :
    RealBox.Contains p (horner z n k) (SynergyAnalytic.expHorner n k x) := by
  induction n generalizing k with
  | zero => exact one_sound
  | succ n ih =>
    have hh := ih (k+1)
    have hn : 0 < k+1 := by omega
    have hs := positiveSub_sound one_sound (divN_sound (RealBox.mul_sound hz hh) hn)
    have hp := (SynergyAnalytic.expHorner_range (n+1) k hx hx1).1
    have he : Max.max 0 (1-x*SynergyAnalytic.expHorner n (k+1) x/((k+1:Nat):ℝ)) =
      SynergyAnalytic.expHorner (n+1) k x := by
      rw [div_eq_mul_inv]
      have eq : 1-x*SynergyAnalytic.expHorner n (k+1) x*(((k+1:Nat):ℝ)⁻¹) =
          SynergyAnalytic.expHorner (n+1) k x := by
        simp only [SynergyAnalytic.expHorner,Nat.cast_add,Nat.cast_one]
        ring
      rw [eq,max_eq_right hp]
    simpa only [horner,he] using hs

theorem widen_exp_sound {z : ProofBox} {x : ℝ}
    (hz : RealBox.Contains p z (SynergyAnalytic.expHorner 48 0 x))
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : RealBox.Contains p (widen z) (Real.exp (-x)) := by
  have hp := RealBox.scale_real_pos p
  have hs : (scale p:ℝ) = (2:ℝ)^128 := by norm_num [scale,p]
  have he := SynergyAnalytic.exp_neg_unit_horner_error hx hx1
  have he' := abs_le.mp he
  have hl := mul_le_mul_of_nonneg_right he'.1 hp.le
  have hu := mul_le_mul_of_nonneg_right he'.2 hp.le
  rw [←hs] at hl hu
  have hq : (1/(scale p:ℝ))*(scale p:ℝ)=1 := by field_simp
  constructor
  · change ((Max.max 0 (z.lo-1):Int):ℝ) ≤ Real.exp (-x)*(scale p:ℝ)
    rw [Int.cast_max,Int.cast_zero,Int.cast_sub,Int.cast_one]
    apply max_le (mul_nonneg (Real.exp_pos _).le hp.le)
    nlinarith [hz.1]
  · change Real.exp (-x)*(scale p:ℝ) ≤ ((z.hi+1:Int):ℝ)
    rw [Int.cast_add,Int.cast_one]
    nlinarith [hz.2]

theorem squares_sound {a : ProofBox} {x : ℝ}
    (ha : RealBox.Contains p a x) (n : Nat) : RealBox.Contains p (squares n a) (x^(2^n)) := by
  induction n generalizing a x with
  | zero => simpa only [squares,pow_zero,pow_one] using ha
  | succ n ih =>
    have hh := ih (RealBox.mul_sound ha ha)
    simpa only [squares,←pow_two,←pow_mul,Nat.pow_succ,Nat.mul_comm] using hh

theorem expNeg_sound {a : ProofBox} {x : ℝ}
    (ha : RealBox.Contains p a x) (hx : 0 ≤ x) (hx64 : x ≤ 64) :
    RealBox.Contains p (expNeg a) (Real.exp (-x)) := by
  have hd := divN_sound ha (by norm_num : 0 < (64:Nat))
  have hx0 : (0:ℝ) ≤ x/64 := by positivity
  have hx1 : x/64 ≤ 1 := by linarith
  have hh := horner_sound hd hx0 hx1 48 0
  have hs := squares_sound (widen_exp_sound hh hx0 hx1) 6
  norm_num only [Nat.cast_ofNat,show (2:Nat)^6=64 by norm_num] at hs
  simpa only [expNeg,SynergyAnalytic.exp_neg_scale64] using hs

#print axioms horner_sound
#print axioms expNeg_sound
end SynergyBasis.Positive
