/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveFold
import RamanujanPV.PackedSieveMaskRefinement
namespace RamanujanPV.PackedSieveCorrect
open PackedSieveKernel PackedSieveFold PackedSieveMaskRefinement SegmentCheckerMath
set_option autoImplicit false
set_option maxHeartbeats 0

theorem allMask_marked {lo hi n : Nat} (hlo : lo≤n) (hhi : n≤hi) :
    (allMask lo hi).testBit (n-lo)=true ↔ Marked hi.sqrt n := by
  rw [allMask,fold_or_bit]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  constructor
  · rintro ⟨j,hj,marked⟩
    have divisor := (divisorMask_sound_complete (by omega : 0<j+2) hlo hhi).mp marked
    exact ⟨j+2,by omega,by omega,divisor⟩
  · rintro ⟨d,hd,hr,hsq,hdiv⟩
    refine ⟨d-2,by omega,?_⟩
    have heq : d-2+2=d := by omega
    rw [heq]
    exact (divisorMask_sound_complete (by omega) hlo hhi).mpr ⟨hsq,hdiv⟩

theorem base_unmarked_prime {r j : Nat} (hj : j<r-1) :
    (allMask 2 r).testBit j=false ↔ Nat.Prime (j+2) := by
  have marked : (allMask 2 r).testBit j=true ↔ ¬Nat.Prime (j+2) := by
    have index : j+2-2=j := by omega
    rw [←index,allMask_marked (by omega) (by omega)]
    exact marked_sqrt_iff_composite (by omega) (by omega)
  constructor
  · intro clear
    by_contra composite
    have impossible := marked.mpr composite
    rw [clear] at impossible
    contradiction
  · intro prime
    apply Bool.eq_false_iff.mpr
    intro bad
    exact (marked.mp bad) prime

theorem compositeMask_iff {lo count n : Nat}
    (hlo2 : 2≤lo) (hlo : lo≤n) (hhi : n≤lo+count-1) :
    (compositeMask lo count).testBit (n-lo)=true ↔ ¬Nat.Prime n := by
  rw [compositeMask,fold_filtered_bit]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  constructor
  · rintro ⟨j,hj,clear,marked⟩ prime
    have divisor := (divisorMask_sound_complete (by omega : 0<j+2) hlo hhi).mp marked
    exact prime_not_marked prime (lo+count-1).sqrt
      ⟨j+2,by omega,by omega,divisor⟩
  · intro composite
    have factor := (marked_sqrt_iff_composite (show 2≤n by omega) hhi).mpr composite
    -- Choose the least prime divisor, avoiding any assumed prime table.
    let d := n.minFac
    have prime : Nat.Prime d := Nat.minFac_prime (by omega)
    have hd : 2≤d := prime.two_le
    have square : d*d≤n := by
      simpa [d,pow_two] using Nat.minFac_sq_le_self (by omega : 0<n) composite
    have rootBound : d≤(lo+count-1).sqrt := by
      apply Nat.le_sqrt.mpr
      nlinarith
    refine ⟨d-2,by omega,?_,?_⟩
    · have h := (base_unmarked_prime (r:=(lo+count-1).sqrt) (j:=d-2) (by omega)).mpr
        (by simpa [Nat.sub_add_cancel hd] using prime)
      exact h
    · have heq : d-2+2=d := by omega
      rw [heq]
      exact (divisorMask_sound_complete (by omega) hlo hhi).mpr ⟨square,Nat.minFac_dvd n⟩

theorem primeBits_prime {lo count i : Nat} (hlo : 2≤lo) (hi : i<count) :
    (primeBits lo count).testBit i=true ↔ Nat.Prime (lo+i) := by
  have bound : lo+i≤lo+count-1 := by omega
  have same : lo+i-lo=i := by omega
  have marked := compositeMask_iff hlo (show lo≤lo+i by omega) bound
  rw [same] at marked
  rw [primeBits,Nat.testBit_ldiff,twoPow_eq,Nat.testBit_two_pow_sub_one]
  simp only [hi,decide_true,Bool.true_and]
  cases hbit : (compositeMask lo count).testBit i <;> simp_all

#print axioms allMask_marked
#print axioms base_unmarked_prime
#print axioms compositeMask_iff
#print axioms primeBits_prime
end RamanujanPV.PackedSieveCorrect
