/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCheckerSource
import RamanujanPV.QuotientSieve

/-! Mathematical refinement target of the actual segmented checker. Every
integer divisor is visited: no prime list, probabilistic test, or unverified
prime/composite label is an input premise. Connecting the actual typed source
loops and concrete executions to these targets remains a separate obligation. -/
namespace RamanujanPV.SegmentCheckerMath
open Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Marked (D n : Nat) : Prop := ∃ d, 2 ≤ d ∧ d ≤ D ∧ d*d ≤ n ∧ d ∣ n

def sweep (lo d : Nat) (flags : Nat → Nat) (i : Nat) : Nat :=
  if d*d ≤ lo+i ∧ d ∣ lo+i then 0 else flags i

/-- The source outer loop successively removes multiples of d=2,3,... . -/
def passes (lo : Nat) : Nat → Nat → Nat
  | 0 => fun _ => 1
  | k+1 => sweep lo (k+2) (passes lo k)

lemma marked_succ (D n : Nat) : Marked (D+1) n ↔
    Marked D n ∨ (2 ≤ D+1 ∧ (D+1)*(D+1) ≤ n ∧ (D+1) ∣ n) := by
  constructor
  · rintro ⟨d,hd,hD,hsq,hdiv⟩
    by_cases h : d ≤ D
    · exact Or.inl ⟨d,hd,h,hsq,hdiv⟩
    · have heq : d = D+1 := by omega
      subst d
      exact Or.inr ⟨hd,hsq,hdiv⟩
  · rintro (⟨d,hd,hD,hsq,hdiv⟩ | ⟨hD,hsq,hdiv⟩)
    · exact ⟨d,hd,by omega,hsq,hdiv⟩
    · exact ⟨D+1,hD,by omega,hsq,hdiv⟩

theorem passes_spec (lo k i : Nat) :
    passes lo k i = if Marked (k+1) (lo+i) then 0 else 1 := by
  classical
  induction k with
  | zero =>
      have h : ¬Marked 1 (lo+i) := by rintro ⟨d,hd,hD,_,_⟩; omega
      simp [passes,h]
  | succ k ih =>
      have hm := marked_succ (k+1) (lo+i)
      by_cases old : Marked (k+1) (lo+i) <;>
        by_cases new : (k+2)*(k+2) ≤ lo+i ∧ (k+2) ∣ lo+i <;>
        simp [passes,sweep,ih,hm,old,new,show 2 ≤ k+1+1 by omega]

theorem prime_not_marked {n : Nat} (prime : Nat.Prime n) (D : Nat) : ¬Marked D n := by
  rintro ⟨d,hd,_,hsq,hdiv⟩
  rcases (Nat.dvd_prime prime).mp hdiv with hone | hself
  · omega
  · subst d
    have hn := prime.two_le
    nlinarith

theorem marked_sqrt_iff_composite {n hi : Nat} (hn : 2 ≤ n) (hhi : n ≤ hi) :
    Marked hi.sqrt n ↔ ¬Nat.Prime n := by
  constructor
  · intro marked prime
    exact prime_not_marked prime _ marked
  · intro composite
    have hsquare := Nat.minFac_sq_le_self (by omega : 0 < n) composite
    refine ⟨n.minFac,?_,?_,?_,Nat.minFac_dvd n⟩
    · exact (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    · apply Nat.le_sqrt.mpr
      nlinarith
    · simpa [pow_two] using hsquare

def finalFlags (lo hi : Nat) : Nat → Nat := passes lo (hi.sqrt-1)

theorem final_flag {lo hi i : Nat} (hlo : 2 ≤ lo) (hindex : lo+i ≤ hi) :
    finalFlags lo hi i = if Nat.Prime (lo+i) then 1 else 0 := by
  have hhi : 0 < hi := by omega
  have hr : 1 ≤ hi.sqrt := Nat.sqrt_pos.mpr hhi
  rw [finalFlags,passes_spec,Nat.sub_add_cancel hr]
  rw [marked_sqrt_iff_composite (by omega) hindex]
  by_cases h : Nat.Prime (lo+i) <;> simp [h]

theorem final_flag_zero_or_one {lo hi i : Nat} (hlo : 2 ≤ lo) (hindex : lo+i ≤ hi) :
    finalFlags lo hi i = 0 ∨ finalFlags lo hi i = 1 := by
  rw [final_flag hlo hindex]
  split <;> simp

def segmentCount (lo hi : Nat) : Nat := ((Icc lo hi).filter Nat.Prime).card

/-- Exact increment, including both integer endpoints. This is the count
interface needed to transport one verified segment to every certificate row. -/
theorem primeCounting_increment {lo hi : Nat} (hlo : 2 ≤ lo) (horder : lo ≤ hi) :
    Nat.primeCounting hi = Nat.primeCounting (lo-1) + segmentCount lo hi := by
  have sets : Nat.primesLE hi = Nat.primesLE (lo-1) ∪ (Icc lo hi).filter Nat.Prime := by
    ext n
    simp only [Nat.primesLE_eq_filter_range,mem_union,mem_filter,mem_range,mem_Icc]
    constructor
    · rintro ⟨hupper,hprime⟩
      by_cases h : n < lo
      · exact Or.inl ⟨by omega,hprime⟩
      · exact Or.inr ⟨⟨by omega,by omega⟩,hprime⟩
    · rintro (⟨hupper,hprime⟩ | ⟨⟨hlower,hupper⟩,hprime⟩) <;> exact ⟨by omega,hprime⟩
  have disjoint : Disjoint (Nat.primesLE (lo-1)) ((Icc lo hi).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro n hleft hright
    have hl := (Nat.mem_primesLE.mp hleft).1
    have hr := (Finset.mem_Icc.mp (Finset.mem_filter.mp hright).1).1
    omega
  rw [←Nat.primesLE_card_eq_primeCounting,sets,Finset.card_union_of_disjoint disjoint,
    Nat.primesLE_card_eq_primeCounting]
  rfl

/-- Natural counterpart of the source's ceil(lo/d)*d preprocessing. -/
def ceilDiv (a b : Nat) : Nat := a/b + if a%b = 0 then 0 else 1
def firstMultiple (lo d : Nat) : Nat := max (ceilDiv lo d*d) (d*d)

lemma ceilDiv_le {a b q : Nat} (hb : 0 < b) (ha : a ≤ q*b) : ceilDiv a b ≤ q := by
  have hdiv := Nat.div_add_mod a b
  unfold ceilDiv
  split_ifs with hzero
  · simp only [Nat.add_zero]
    by_contra! hq
    have hh : q+1 ≤ a/b := by omega
    nlinarith
  · have hmod : 0 < a%b := Nat.pos_of_ne_zero hzero
    have hq : a/b < q := by
      by_contra! hh
      nlinarith [hdiv]
    omega

theorem first_divisible (lo d : Nat) : d ∣ firstMultiple lo d := by
  unfold firstMultiple
  rcases le_total (ceilDiv lo d*d) (d*d) with h | h
  · rw [max_eq_right h]; exact dvd_mul_right d d
  · rw [max_eq_left h]; exact dvd_mul_left d (ceilDiv lo d)

theorem first_lower {lo d : Nat} (hd : 0 < d) :
    lo ≤ firstMultiple lo d ∧ d*d ≤ firstMultiple lo d := by
  have hdiv := Nat.div_add_mod lo d
  have hmod := Nat.mod_lt lo hd
  have hceil : lo ≤ ceilDiv lo d*d := by
    unfold ceilDiv
    split_ifs with hzero <;> nlinarith
  exact ⟨hceil.trans (le_max_left _ _),le_max_right _ _⟩

theorem first_minimal {lo d n : Nat} (hd : 0 < d)
    (hlo : lo ≤ n) (hsquare : d*d ≤ n) (hdiv : d ∣ n) : firstMultiple lo d ≤ n := by
  apply max_le _ hsquare
  have h := ceilDiv_le hd (show lo ≤ n/d*d by simpa [Nat.div_mul_cancel hdiv] using hlo)
  exact (Nat.mul_le_mul_right d h).trans (Nat.div_mul_le_self n d)

#print axioms final_flag
#print axioms primeCounting_increment
#print axioms first_minimal
end RamanujanPV.SegmentCheckerMath
