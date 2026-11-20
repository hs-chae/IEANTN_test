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

noncomputable def specValue (D n : Nat) : Nat := by
  classical
  exact if Marked D n then 0 else 1

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
    passes lo k i = specValue (k+1) (lo+i) := by
  classical
  induction k with
  | zero =>
      have h : ¬Marked 1 (lo+i) := by rintro ⟨d,hd,hD,_,_⟩; omega
      simp [passes,specValue,h]
  | succ k ih =>
      have hm := marked_succ (k+1) (lo+i)
      by_cases old : Marked (k+1) (lo+i) <;>
        by_cases new : (k+2)*(k+2) ≤ lo+i ∧ (k+2) ∣ lo+i <;>
        simp [passes,sweep,ih,specValue,hm,old,new,show 2 ≤ k+1+1 by omega]

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
  classical
  have hhi : 0 < hi := by omega
  have hr : 1 ≤ hi.sqrt := Nat.sqrt_pos.mpr hhi
  rw [finalFlags,passes_spec,Nat.sub_add_cancel hr]
  unfold specValue
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

/-- Exact unbounded-integer operations in the source's first-variable setup. -/
def sourceFirst (lo d : Nat) : Nat :=
  let start := lo/d*d
  let next := if start < lo then start+d else start
  if next < d*d then d*d else next

lemma select_max (a b : Nat) : (if a < b then b else a) = max a b := by
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (by omega)).symm

theorem sourceFirst_eq_first {lo d : Nat} (hd : 0 < d) : sourceFirst lo d = firstMultiple lo d := by
  have hdiv : lo/d*d + lo%d = lo := by simpa [Nat.mul_comm] using Nat.div_add_mod lo d
  have hbase := Nat.div_mul_le_self lo d
  unfold sourceFirst firstMultiple ceilDiv
  rw [select_max]
  congr 1
  by_cases hzero : lo%d = 0
  · have heq : lo/d*d = lo := by omega
    simp [hzero,heq]
  · have hpositive : 0 < lo%d := Nat.pos_of_ne_zero hzero
    have hless : lo/d*d < lo := by omega
    simp [hzero,hless,Nat.add_mul]

def markCount (lo hi d : Nat) : Nat :=
  if firstMultiple lo d ≤ hi then (hi-firstMultiple lo d)/d+1 else 0

def Visited (first d count n : Nat) : Prop := ∃ k, k < count ∧ n = first+k*d

theorem visited_iff {lo hi d n : Nat} (hd : 0 < d) (hlo : lo ≤ n) (hhi : n ≤ hi) :
    Visited (firstMultiple lo d) d (markCount lo hi d) n ↔ d*d ≤ n ∧ d ∣ n := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    refine ⟨?_,dvd_add (first_divisible lo d) (dvd_mul_left d k)⟩
    exact (first_lower hd).2.trans (Nat.le_add_right _ _)
  · rintro ⟨hsquare,hdiv⟩
    have hfirst : firstMultiple lo d ≤ n := first_minimal hd hlo hsquare hdiv
    have hfirstHi : firstMultiple lo d ≤ hi := hfirst.trans hhi
    have hdiff : d ∣ n-firstMultiple lo d := Nat.dvd_sub hdiv (first_divisible lo d)
    refine ⟨(n-firstMultiple lo d)/d,?_,?_⟩
    · unfold markCount
      rw [if_pos hfirstHi]
      have h : (n-firstMultiple lo d)/d ≤ (hi-firstMultiple lo d)/d :=
        Nat.div_le_div_right (Nat.sub_le_sub_right hhi (firstMultiple lo d))
      omega
    · rw [Nat.div_mul_cancel hdiff,Nat.add_sub_of_le hfirst]

def erasePrefix (lo first d : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, flags => flags
  | k+1, flags => Function.update (erasePrefix lo first d k flags) (first+k*d-lo) 0

theorem erasePrefix_cases {lo first d n : Nat} (hfirst : lo ≤ first) (hn : lo ≤ n)
    (count : Nat) (flags : Nat → Nat) :
    (Visited first d count n → erasePrefix lo first d count flags (n-lo) = 0) ∧
    (¬Visited first d count n → erasePrefix lo first d count flags (n-lo) = flags (n-lo)) := by
  induction count with
  | zero =>
      constructor
      · rintro ⟨k,hk,_⟩; omega
      · intro _; rfl
  | succ count ih =>
      have hs : lo ≤ first+count*d := hfirst.trans (Nat.le_add_right _ _)
      by_cases heq : n = first+count*d
      · subst n
        constructor
        · intro _; simp [erasePrefix]
        · intro absent; exact (absent ⟨count,by omega,rfl⟩).elim
      · have hindex : n-lo ≠ first+count*d-lo := by omega
        have visited : Visited first d (count+1) n ↔ Visited first d count n := by
          constructor
          · rintro ⟨k,hk,hvalue⟩
            have hk' : k < count := by
              by_contra bad
              have hkc : k = count := by omega
              apply heq
              simpa [hkc] using hvalue
            exact ⟨k,hk',hvalue⟩
          · rintro ⟨k,hk,hvalue⟩; exact ⟨k,by omega,hvalue⟩
        constructor
        · intro present
          simpa [erasePrefix,Function.update_of_ne hindex] using ih.1 (visited.mp present)
        · intro absent
          simpa [erasePrefix,Function.update_of_ne hindex] using ih.2 (fun v => absent (visited.mpr v))

/-- The exact finite sequence of indexed source stores implements the complete
divisibility sweep, including the empty inner loop and interval endpoints. -/
theorem erased_segment_is_sweep {lo hi d n : Nat} (hd : 0 < d) (hlo : lo ≤ n) (hhi : n ≤ hi)
    (flags : Nat → Nat) :
    erasePrefix lo (firstMultiple lo d) d (markCount lo hi d) flags (n-lo) =
      sweep lo d flags (n-lo) := by
  have cases := erasePrefix_cases (d := d) (first_lower hd).1 hlo (markCount lo hi d) flags
  have equiv := visited_iff hd hlo hhi
  by_cases erased : d*d ≤ n ∧ d ∣ n
  · have h := cases.1 (equiv.mpr erased)
    simpa [sweep,Nat.add_sub_of_le hlo,erased] using h

theorem first_upper {lo hi d : Nat} (hlo : lo ≤ hi) (hsquare : d*d ≤ hi) :
    firstMultiple lo d ≤ hi+d := by
  have hbase := Nat.div_mul_le_self lo d
  have hceil : ceilDiv lo d*d ≤ lo+d := by
    unfold ceilDiv
    split_ifs <;> nlinarith
  exact max_le (by omega) (by omega)

theorem mark_member_upper {lo hi d k : Nat} (hd : 0 < d) (hk : k < markCount lo hi d) :
    firstMultiple lo d+k*d ≤ hi := by
  unfold markCount at hk
  split_ifs at hk with hfirst
  · have hle : k ≤ (hi-firstMultiple lo d)/d := by omega
    have hm := (Nat.le_div_iff_mul_le hd).mp hle
    omega
  · omega

theorem mark_end_gt {lo hi d : Nat} (hd : 0 < d) :
    hi < firstMultiple lo d+markCount lo hi d*d := by
  unfold markCount
  split_ifs with hfirst
  · have hdiv : (hi-firstMultiple lo d)/d*d+(hi-firstMultiple lo d)%d = hi-firstMultiple lo d := by
      simpa [Nat.mul_comm] using Nat.div_add_mod (hi-firstMultiple lo d) d
    have hmod := Nat.mod_lt (hi-firstMultiple lo d) hd
    have hsub := Nat.sub_add_cancel hfirst
    nlinarith
  · omega

theorem mark_end_upper {lo hi d : Nat} (hlo : lo ≤ hi) (hsquare : d*d ≤ hi) :
    firstMultiple lo d+markCount lo hi d*d ≤ hi+d := by
  unfold markCount
  split_ifs with hfirst
  · have hdiv := Nat.div_mul_le_self (hi-firstMultiple lo d) d
    have hsub := Nat.sub_add_cancel hfirst
    nlinarith
  · simpa using first_upper hlo hsquare
  · have h := cases.2 (fun marked => erased (equiv.mp marked))
    simpa [sweep,Nat.add_sub_of_le hlo,erased] using h

#print axioms final_flag
#print axioms primeCounting_increment
#print axioms first_minimal
#print axioms erased_segment_is_sweep
end RamanujanPV.SegmentCheckerMath
