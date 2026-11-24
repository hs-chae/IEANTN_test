/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import RamanujanPV.QuotientSieve

/-! Application arithmetic and index applicability for the actual quotient-sieve
source. These are finite-cardinality and natural-number proofs, with explicit
argument domains. They do not assume source execution or any prime-count output. -/
namespace RamanujanPV.QuotientWordBounds
open RamanujanPV.QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Every stored invariant value counts a subset of the integers 2..v. -/
theorem total_le_argument (p v : Nat) : total p v ≤ v := by
  have hs : survivors p v ⊆ Finset.Icc 2 v := Finset.filter_subset _ _
  have hc := Finset.card_le_card hs
  have hi : (Finset.Icc 2 v).card ≤ v := by rw [Nat.card_Icc]; omega
  exact hc.trans hi

theorem total_le_input {p v N : Nat} (hv : v ≤ N) : total p v ≤ N :=
  (total_le_argument p v).trans hv

/-- Both actual C subtraction guards follow from the invariant's set bijection;
no modular subtraction or saturating subtraction is used to mask underflow. -/
theorem subtraction_guards {p v : Nat} (hp : Nat.Prime p) (hsquare : p*p ≤ v) :
    total p (p-1) ≤ total p (v/p) ∧
      total p (v/p)-total p (p-1) ≤ total p v := by
  have hquot : p ≤ v/p := (Nat.le_div_iff_mul_le hp.pos).mpr hsquare
  have hsubset := survivors_bound_mono (p:=p) (show p-1 ≤ v/p by omega)
  have hbefore : total p (p-1) ≤ total p (v/p) := Finset.card_le_card hsubset
  have htail : (tail p (v/p)).card = total p (v/p)-total p (p-1) :=
    Finset.card_sdiff_of_subset hsubset
  have hremoved : (removed p v).card = total p (v/p)-total p (p-1) :=
    (removed_card (v:=v) hp).trans htail
  have hcard : (removed p v).card ≤ total p v := by
    unfold removed total
    exact Finset.card_le_card Finset.sdiff_subset
  exact ⟨hbefore,hremoved.symm ▸ hcard⟩

/-- Above the integer square root, division lands in the small table. -/
theorem quotient_small_of_above_sqrt {N r d : Nat}
    (hroot : N < (r+1)*(r+1)) (hd : r < d) : N/d ≤ r := by
  by_contra! hq
  have hq' : r+1 ≤ N/d := by omega
  have hd' : r+1 ≤ d := by omega
  have hm := Nat.mul_le_mul hq' hd'
  have hdiv := Nat.div_mul_le_self N d
  omega

/-- Full numeric domains of the source large-loop body, including the two
uint64 products and both branches of its quotient-table read. -/
theorem word_index_bounds {N r p i : Nat}
    (hN : N ≤ 2000000000000) (hrootLo : r*r ≤ N)
    (hrootHi : N < (r+1)*(r+1)) (hp2 : 2 ≤ p) (hpr : p ≤ r)
    (hi1 : 1 ≤ i) (histop : i ≤ min r (N/(p*p))) :
    p*p < 2^64 ∧ i*p < 2^64 ∧ i*p ≤ N ∧ i < i*p ∧
      p*p ≤ N/i ∧
      (r < i*p → 1 ≤ N/(i*p) ∧ N/(i*p) ≤ r) ∧
      (i*p ≤ r → i < i*p ∧ i*p ≤ r) := by
  have hir : i ≤ r := (le_min_iff.mp histop).1
  have hiq : i ≤ N/(p*p) := (le_min_iff.mp histop).2
  have hpSquare : p*p ≤ N := (Nat.mul_le_mul hpr hpr).trans hrootLo
  have hip : i*p ≤ N := (Nat.mul_le_mul hir hpr).trans hrootLo
  have hipgt : i < i*p := by nlinarith [hi1,hp2]
  have hppos : 0 < p*p := by positivity
  have hi0 : 0 < i := by omega
  have hlimit : i*(p*p) ≤ N := (Nat.le_div_iff_mul_le hppos).mp hiq
  have hsquare : p*p ≤ N/i := by
    apply (Nat.le_div_iff_mul_le hi0).mpr
    simpa [Nat.mul_comm] using hlimit
  refine ⟨hpSquare.trans_lt (hN.trans_lt (by norm_num)),
    hip.trans_lt (hN.trans_lt (by norm_num)),hip,hipgt,hsquare,?_,?_⟩
  · intro hbig
    have hip0 : 0 < i*p := by positivity
    have hlo : 1 ≤ N/(i*p) := (Nat.le_div_iff_mul_le hip0).mpr (by simpa using hip)
    exact ⟨hlo,quotient_small_of_above_sqrt hrootHi hbig⟩
  · intro hsmall
    exact ⟨hipgt,hsmall⟩

/-- The checked integer square-root definition supplies the source body domain. -/
theorem word_index_bounds_sqrt {N r p i : Nat}
    (hN : N ≤ 2000000000000) (hr : r = Nat.sqrt N)
    (hp2 : 2 ≤ p) (hpr : p ≤ r) (hi1 : 1 ≤ i)
    (histop : i ≤ min r (N/(p*p))) :
    p*p < 2^64 ∧ i*p < 2^64 ∧ i*p ≤ N ∧ i < i*p ∧
      p*p ≤ N/i ∧
      (r < i*p → 1 ≤ N/(i*p) ∧ N/(i*p) ≤ r) ∧
      (i*p ≤ r → i < i*p ∧ i*p ≤ r) := by
  apply word_index_bounds hN
  · simpa [hr] using Nat.sqrt_le N
  · simpa [hr,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  · exact hp2
  · exact hpr
  · exact hi1
  · exact histop

/-- Invariant values fit uint64 at every actual source argument at most N. -/
theorem table_value_word_bound {N p v : Nat} (hN : N ≤ 2000000000000) (hv : v ≤ N) :
    total p v < 2^64 := (total_le_input hv).trans_lt (hN.trans_lt (by norm_num))

/-- The invariant itself supplies both subtraction guards at every visited
large-table cell; the source's explicit failure branches cannot trigger. -/
theorem large_cell_subtraction_guards {N r p i : Nat}
    (hp : Nat.Prime p) (hi1 : 1 ≤ i)
    (histop : i ≤ min r (N/(p*p))) :
    total p (p-1) ≤ total p ((N/i)/p) ∧
      total p ((N/i)/p)-total p (p-1) ≤ total p (N/i) := by
  have hp0 : 0 < p := hp.pos
  have hiq : i ≤ N/(p*p) := (le_min_iff.mp histop).2
  have hppos : 0 < p*p := by positivity
  have hlimit : i*(p*p) ≤ N := (Nat.le_div_iff_mul_le hppos).mp hiq
  have hsquare : p*p ≤ N/i := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < i)).mpr
    simpa [Nat.mul_comm] using hlimit
  exact subtraction_guards hp hsquare

#print axioms total_le_argument
#print axioms subtraction_guards
#print axioms word_index_bounds_sqrt
#print axioms table_value_word_bound
#print axioms large_cell_subtraction_guards
end RamanujanPV.QuotientWordBounds
