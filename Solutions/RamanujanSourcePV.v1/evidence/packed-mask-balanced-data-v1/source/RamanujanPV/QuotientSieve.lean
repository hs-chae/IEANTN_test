/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.PrimeCount
namespace RamanujanPV.QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The Lucy quotient-table invariant: retain every prime, and retain a
composite exactly when its smallest prime factor has not yet been processed. -/
def Survives (p n : Nat) : Prop := Nat.Prime n ∨p≤n.minFac
instance (p n : Nat) : Decidable (Survives p n) := inferInstanceAs (Decidable (Nat.Prime n ∨p≤n.minFac))
def survivors (p v : Nat) : Finset Nat := (Finset.Icc 2 v).filter (Survives p)
def total (p v : Nat) : Nat := (survivors p v).card

/-- The least prime factor of a product whose remaining factor is p-rough. -/
theorem minFac_product {p k : Nat} (hp : Nat.Prime p) (hk : p≤k.minFac) :
    (p*k).minFac=p := by
  apply Nat.le_antisymm (Nat.minFac_le_of_dvd hp.two_le (by exact ⟨k,rfl⟩))
  apply (Nat.le_minFac.mpr ?_).resolve_left
  · intro impossible
    have hprod : 2≤p*k := by
      have kpos := Nat.minFac_pos k
      have kne : k≠0 := by
        intro hz
        subst k
        simp at impossible
      have : 1≤k := Nat.one_le_iff_ne_zero.mpr kne
      nlinarith [hp.two_le]
    omega
  · intro q hq divides
    rcases hq.dvd_mul.mp divides with left|right
    · rcases (Nat.dvd_prime hp).mp left with one|same
      · exact False.elim (hq.ne_one one)
      · omega
    · exact hk.trans (Nat.minFac_le_of_dvd hq.two_le right)

theorem survives_mono {p n : Nat} : Survives (p+1) n →Survives p n := by
  intro h
  rcases h with h|h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem dropped_iff {p n : Nat} :
    Survives p n ∧¬Survives (p+1) n ↔ ¬Nat.Prime n ∧n.minFac=p := by
  simp only [Survives,not_or,not_le]
  constructor
  · rintro ⟨hp|hmin,hn,hnext⟩
    · contradiction
    · exact ⟨hn,by omega⟩
  · rintro ⟨hn,eq⟩
    exact ⟨Or.inr (by omega),hn,by omega⟩

/-- Exact multiplicative description of the entries removed at a prime p. -/
theorem dropped_product {p n : Nat} (hp : Nat.Prime p) (hn : 2≤n) :
    (Survives p n ∧¬Survives (p+1) n) ↔
      ∃k, p≤k ∧p≤k.minFac ∧n=p*k := by
  rw [dropped_iff]
  constructor
  · rintro ⟨composite,minEq⟩
    let k := n/p
    have dvd : p∣n := by rw [←minEq];exact Nat.minFac_dvd n
    have keq : n=p*k := (Nat.mul_div_cancel' dvd).symm
    have lower : p≤k := by
      have bound := Nat.minFac_le_div (by omega : 0<n) composite
      simpa [minEq,k] using bound
    have rough : p≤k.minFac := by
      have k2 : 2≤k := hp.two_le.trans lower
      have prime := Nat.minFac_prime (by omega : k≠1)
      have kd : k.minFac∣n := (Nat.minFac_dvd k).trans (by rw [keq];exact Nat.dvd_mul_left k p)
      have bound := Nat.minFac_le_of_dvd prime.two_le kd
      simpa [minEq] using bound
    exact ⟨k,lower,rough,keq⟩
  · rintro ⟨k,lower,rough,keq⟩
    have minEq : n.minFac=p := by rw [keq];exact minFac_product hp rough
    have gt : p<n := by rw [keq];nlinarith [hp.two_le]
    exact ⟨(Nat.not_prime_iff_minFac_lt hn).mpr (by omega),minEq⟩

/-- Prime detection uses the adjacent small-table difference, rather than
assuming an unverified list of primes. -/
theorem survives_self_iff {p : Nat} (hp : 2≤p) : Survives p p ↔Nat.Prime p := by
  constructor
  · intro h
    rcases h with prime|rough
    · exact prime
    · by_contra composite
      have low := (Nat.not_prime_iff_minFac_lt hp).mp composite
      omega
  · exact Or.inl

/-- Before any prime is processed, each integer2..v is present. -/
theorem total_initial (v : Nat) : total 2 v=v-1 := by
  have all : survivors 2 v=Finset.Icc 2 v := by
    apply Finset.filter_true_of_mem
    intro n hn
    have n2 := (Finset.mem_Icc.mp hn).1
    exact Or.inr (Nat.minFac_prime (by omega : n≠1)).two_le
  simp [total,all,Nat.card_Icc]

theorem survivors_bound_mono {p a b : Nat} (h : a≤b) : survivors p a ⊆survivors p b := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨range,keep⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp range).1,(Finset.mem_Icc.mp range).2.trans h⟩,keep⟩

theorem survivors_step_subset (p v : Nat) : survivors (p+1) v ⊆survivors p v := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨range,keep⟩
  exact Finset.mem_filter.mpr ⟨range,survives_mono keep⟩

theorem survives_above {p k : Nat} (lower : p≤k) :
    Survives p k ↔p≤k.minFac := by
  constructor
  · rintro (prime|rough)
    · simpa [prime.minFac_eq] using lower
    · exact rough
  · exact Or.inr

def tail (p v : Nat) : Finset Nat := survivors p v \survivors p (p-1)
def removed (p v : Nat) : Finset Nat := survivors p v \survivors (p+1) v

theorem mem_tail {p v k : Nat} (hp : 2≤p) :
    k∈tail p v ↔p≤k ∧k≤v ∧p≤k.minFac := by
  constructor
  · intro h
    rcases Finset.mem_sdiff.mp h with ⟨hk,hn⟩
    rcases Finset.mem_filter.mp hk with ⟨range,keep⟩
    have bounds := Finset.mem_Icc.mp range
    have lower : p≤k := by
      by_contra bad
      apply hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨bounds.1,by omega⟩,keep⟩
    exact ⟨lower,bounds.2,(survives_above lower).mp keep⟩
  · rintro ⟨lower,upper,rough⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,upper⟩,Or.inr rough⟩
    · intro bad
      have range := Finset.mem_Icc.mp (Finset.mem_filter.mp bad).1
      omega

theorem mem_removed {p v n : Nat} :
    n∈removed p v ↔2≤n ∧n≤v ∧Survives p n ∧¬Survives (p+1) n := by
  simp only [removed,survivors,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_Icc]
  tauto

/-- The exact Lucy subtraction is a proved bijection: the deleted composite
m corresponds to k=m/p among the surviving entries from p through floor(v/p). -/
theorem removed_card {p v : Nat} (hp : Nat.Prime p) :
    (removed p v).card=(tail p (v/p)).card := by
  symm
  apply Finset.card_bij (fun k _=>p*k)
  · intro k member
    rcases (mem_tail hp.two_le).mp member with ⟨lower,upper,rough⟩
    have productUpper : p*k≤v := by
      have mul := (Nat.le_div_iff_mul_le hp.pos).mp upper
      simpa [Nat.mul_comm] using mul
    have productLower : 2≤p*k := by nlinarith [hp.two_le]
    have dropped := (dropped_product hp productLower).mpr ⟨k,lower,rough,rfl⟩
    exact mem_removed.mpr ⟨productLower,productUpper,dropped⟩
  · intro a ha b hb eq
    nlinarith [hp.pos]
  · intro n member
    rcases mem_removed.mp member with ⟨n2,upper,dropped⟩
    obtain ⟨k,lower,rough,eq⟩ := (dropped_product hp n2).mp dropped
    refine ⟨k,(mem_tail hp.two_le).mpr ⟨lower,?_,rough⟩,eq.symm⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    nlinarith [upper]

/-- Proven numerical table transition, with natural subtraction justified by
finite-set inclusions. No externally supplied prime-count values occur. -/
theorem total_step {p v : Nat} (hp : Nat.Prime p) (square : p*p≤v) :
    total (p+1) v=total p v-(total p (v/p)-total p (p-1)) := by
  have quotLower : p≤v/p := (Nat.le_div_iff_mul_le hp.pos).mpr square
  have smallSubset := survivors_bound_mono (p:=p) (show p-1≤v/p by omega)
  have nextSubset := survivors_step_subset p v
  have drop := removed_card (v:=v) hp
  have left : (removed p v).card=total p v-total (p+1) v :=
    Finset.card_sdiff_of_subset nextSubset
  have right : (tail p (v/p)).card=total p (v/p)-total p (p-1) :=
    Finset.card_sdiff_of_subset smallSubset
  have le := Finset.card_le_card nextSubset
  change total (p+1) v≤total p v at le
  omega

theorem total_prime_detection {p : Nat} (hp : 2≤p) :
    total p p=total p (p-1)+(if Nat.Prime p then 1 else 0) := by
  have interval : Finset.Icc 2 p=insert p (Finset.Icc 2 (p-1)) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have absent : p∉survivors p (p-1) := by
    intro h
    have range := Finset.mem_Icc.mp (Finset.mem_filter.mp h).1
    omega
  unfold total at *
  unfold survivors
  rw [interval,Finset.filter_insert]
  simp only [survives_self_iff hp]
  have absentActual : p∉Finset.filter (Survives p) (Finset.Icc 2 (p-1)) := absent
  by_cases prime : Nat.Prime p
  · simp [prime,absentActual]
  · simp [prime]

/-- The actual source test small[p]!=small[p-1] is equivalent to primality
when its two entries satisfy the invariant. -/
theorem detected_iff_prime {p : Nat} (hp : 2≤p) :
    total p p≠total p (p-1) ↔Nat.Prime p := by
  rw [total_prime_detection hp]
  by_cases prime : Nat.Prime p <;> simp [prime]

theorem total_skip_composite {p v : Nat} (hp : ¬Nat.Prime p) :
    total (p+1) v=total p v := by
  unfold total
  apply congrArg Finset.card
  apply Finset.Subset.antisymm (survivors_step_subset p v)
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨range,keep⟩
  apply Finset.mem_filter.mpr
  refine ⟨range,?_⟩
  by_contra removed
  have drop := dropped_iff.mp ⟨keep,removed⟩
  have n2 := (Finset.mem_Icc.mp range).1
  have prime := Nat.minFac_prime (by omega : n≠1)
  rw [drop.2] at prime
  exact hp prime

theorem total_skip_below_square {p v : Nat} (square : v<p*p) :
    total (p+1) v=total p v := by
  unfold total
  apply congrArg Finset.card
  apply Finset.Subset.antisymm (survivors_step_subset p v)
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨range,keep⟩
  apply Finset.mem_filter.mpr
  refine ⟨range,?_⟩
  by_contra removed
  have drop := dropped_iff.mp ⟨keep,removed⟩
  have bounds := Finset.mem_Icc.mp range
  have minSquare := Nat.minFac_sq_le_self (by omega : 0<n) drop.1
  rw [drop.2] at minSquare
  nlinarith

/-- At the completed square-root frontier, only actual primes survive. -/
theorem total_final {p v : Nat} (square : v<p*p) :
    total p v=Nat.primeCounting v := by
  have eq : survivors p v=Nat.primesLE v := by
    ext n
    simp only [survivors,Finset.mem_filter,Finset.mem_Icc,
      Nat.primesLE_eq_filter_range,Finset.mem_range]
    constructor
    · rintro ⟨⟨n2,upper⟩,prime|rough⟩
      · exact ⟨by omega,prime⟩
      · have prime : Nat.Prime n := by
          by_contra composite
          have minSquare := Nat.minFac_sq_le_self (by omega : 0<n) composite
          nlinarith
        exact ⟨by omega,prime⟩
    · rintro ⟨upper,prime⟩
      exact ⟨⟨prime.two_le,by omega⟩,Or.inl prime⟩
  unfold total
  rw [eq,Nat.primesLE_card_eq_primeCounting]

/-- A total update valid at every table argument; exactly the guarded
subtraction in the real implementation. -/
theorem total_update {p v : Nat} (hp : 2≤p) :
    total (p+1) v =
      if total p p=total p (p-1) ∨v<p*p then total p v
      else total p v-(total p (v/p)-total p (p-1)) := by
  by_cases prime : Nat.Prime p
  · have detected := (detected_iff_prime hp).mpr prime
    by_cases square : v<p*p
    · simp [square,total_skip_below_square square]
    · rw [if_neg (by simp [detected,square])]
      exact total_step (v:=v) prime (by omega)
  · have equal : total p p=total p (p-1) := by
      by_contra notEqual
      exact prime ((detected_iff_prime hp).mp notEqual)
    simp [equal,total_skip_composite prime]

/-- A checked composite gap permits jumping directly between the candidate
prime stages used by the production quotient-table algorithm. -/
theorem total_jump {a b : Nat} (ordered : a≤b)
    (noPrimes : ∀q, a≤q →q<b →¬Nat.Prime q) (v : Nat) :
    total a v=total b v := by
  unfold total
  apply congrArg Finset.card
  ext n
  simp only [survivors,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨bounds,prime|rough⟩
    · exact ⟨bounds,Or.inl prime⟩
    · have upperRough : b≤n.minFac := by
        by_contra below
        have prime := Nat.minFac_prime (by omega : n≠1)
        exact noPrimes n.minFac rough (by omega) prime
      exact ⟨bounds,Or.inr upperRough⟩
  · rintro ⟨bounds,prime|rough⟩
    · exact ⟨bounds,Or.inl prime⟩
    · exact ⟨bounds,Or.inr (ordered.trans rough)⟩

def checkFactors : Nat→List Nat→Bool
  | _,[] => true
  | first,d::ds => decide (2≤d ∧d<first ∧first%d=0) && checkFactors (first+1) ds

theorem checkFactors_sound (first : Nat) (factors : List Nat)
    (checked : checkFactors first factors=true) :
    ∀q, first≤q →q<first+factors.length →¬Nat.Prime q := by
  induction factors generalizing first with
  | nil => intro q low high; simp at high;omega
  | cons d ds ih =>
    have clauses : (2≤d ∧d<first ∧first%d=0) ∧checkFactors (first+1) ds=true := by
      simpa [checkFactors] using checked
    intro q low high prime
    by_cases eq : q=first
    · subst q
      exact (Nat.prime_def_lt'.mp prime).2 d clauses.1.1 clauses.1.2.1
        (Nat.dvd_of_mod_eq_zero clauses.1.2.2)
    · exact ih (first+1) clauses.2 q (by omega) (by simp at high;omega) prime

theorem jump_from_factors (first : Nat) (factors : List Nat)
    (checked : checkFactors first factors=true) (v : Nat) :
    total first v=total (first+factors.length) v :=
  total_jump (by omega) (checkFactors_sound first factors checked) v

/-- Once a table cell lies beyond its own square-root frontier, further
prime stages never change it and its exact value is already pi(v). -/
theorem finish_value {p v y : Nat} (square : v<p*p) (known : total p v=y) :
    Nat.primeCounting v=y := by
  rwa [total_final square] at known

theorem use_finished {p v y : Nat} (square : v<p*p) (known : Nat.primeCounting v=y) :
    total p v=y := by
  rwa [total_final square]

#print axioms total_jump
#print axioms checkFactors_sound
#print axioms jump_from_factors
#print axioms finish_value
#print axioms total_prime_detection
#print axioms total_skip_composite
#print axioms total_skip_below_square
#print axioms total_final
#print axioms total_update
#print axioms removed_card
#print axioms total_step
#print axioms minFac_product
#print axioms dropped_product
#print axioms survives_self_iff
#print axioms total_initial
end RamanujanPV.QuotientSieve
