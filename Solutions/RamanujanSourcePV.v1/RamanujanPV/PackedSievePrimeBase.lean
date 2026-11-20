/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveCorrect
import RamanujanPV.PackedSievePrimitiveBits

/-! A certified explicit prime base. Existing compositeMask already skips
composite divisors. This variant folds only an explicitly represented list,
whose membership is proved against the canonical small primeBits bitmap.
No unverified prime list, native execution leaf or source-PV claim is used. -/
namespace RamanujanPV.PackedSievePrimeBase
open PackedSieveKernel PackedSieveFold PackedSieveCorrect PackedSieveMaskRefinement
open SegmentCheckerMath
set_option autoImplicit false
set_option maxHeartbeats 0

def baseBitmap (ps : List Nat) : Nat :=
  ps.foldl (fun bits p => bits ||| twoPow (p-2)) 0

def rangeCheck (r : Nat) (ps : List Nat) : Bool :=
  ps.all (fun p => decide (2≤p ∧ p≤r))

structure BaseCertificate (r : Nat) (ps : List Nat) : Prop where
  bounds : rangeCheck r ps=true
  bitmap : baseBitmap ps=primeBits 2 (r-1)

theorem range_bounds {r p : Nat} {ps : List Nat}
    (checked : rangeCheck r ps=true) (member : p∈ps) : 2≤p ∧ p≤r := by
  have all := List.all_eq_true.mp checked p member
  exact of_decide_eq_true all

theorem baseBitmap_bit (ps : List Nat) (i : Nat) :
    (baseBitmap ps).testBit i=true ↔ ∃p∈ps,p-2=i := by
  rw [baseBitmap,fold_or_bit]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,twoPow_eq,
    Nat.testBit_two_pow,decide_eq_true_eq]

theorem certified_membership {r p : Nat} {ps : List Nat}
    (certificate : BaseCertificate r ps) :
    p∈ps ↔ 2≤p ∧ p≤r ∧ Nat.Prime p := by
  constructor
  · intro member
    obtain ⟨lower,upper⟩ := range_bounds certificate.bounds member
    have bit := (baseBitmap_bit ps (p-2)).mpr ⟨p,member,rfl⟩
    rw [certificate.bitmap] at bit
    have prime := (primeBits_prime (lo:=2) (count:=r-1) (i:=p-2)
      (by omega) (by omega)).mp bit
    exact ⟨lower,upper,by simpa [Nat.add_sub_of_le lower] using prime⟩
  · rintro ⟨lower,upper,prime⟩
    have bit : (primeBits 2 (r-1)).testBit (p-2)=true :=
      (primeBits_prime (lo:=2) (count:=r-1) (i:=p-2) (by omega) (by omega)).mpr
        (by simpa [Nat.add_sub_of_le lower] using prime)
    rw [←certificate.bitmap,baseBitmap_bit] at bit
    obtain ⟨q,hq,same⟩ := bit
    have qlower := (range_bounds certificate.bounds hq).1
    have equal : q=p := by omega
    exact equal ▸ hq

def compositeFromList (lo count : Nat) (ps : List Nat) : Nat :=
  ps.foldl (fun bits p=>bits ||| divisorMask lo (lo+count-1) p) 0

def bitsFromList (lo count : Nat) (ps : List Nat) : Nat :=
  Nat.ldiff (twoPow count-1) (compositeFromList lo count ps)

def primitiveFromList (lo count : Nat) (ps : List Nat) : Nat :=
  let mask:=twoPow count-1
  mask ^^^ (mask &&& compositeFromList lo count ps)

theorem list_composite_iff {lo count n : Nat} {ps : List Nat}
    (certificate : BaseCertificate (lo+count-1).sqrt ps)
    (hlo2 : 2≤lo) (hlo : lo≤n) (hhi : n≤lo+count-1) :
    (compositeFromList lo count ps).testBit (n-lo)=true ↔ ¬Nat.Prime n := by
  rw [compositeFromList,fold_or_bit]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or]
  constructor
  · rintro ⟨p,member,marked⟩ prime
    have bounded := (certified_membership certificate).mp member
    have divisor := (divisorMask_sound_complete (by omega : 0<p) hlo hhi).mp marked
    exact prime_not_marked prime (lo+count-1).sqrt
      ⟨p,bounded.1,bounded.2.1,divisor⟩
  · intro composite
    let p:=n.minFac
    have prime : Nat.Prime p := Nat.minFac_prime (by omega)
    have square : p*p≤n := by
      simpa [p,pow_two] using Nat.minFac_sq_le_self (by omega : 0<n) composite
    have upper : p≤(lo+count-1).sqrt := by
      apply Nat.le_sqrt.mpr
      nlinarith
    have member : p∈ps := (certified_membership certificate).mpr ⟨prime.two_le,upper,prime⟩
    exact ⟨p,member,(divisorMask_sound_complete prime.pos hlo hhi).mpr
      ⟨square,Nat.minFac_dvd n⟩⟩

theorem bitsFromList_prime {lo count i : Nat} {ps : List Nat}
    (certificate : BaseCertificate (lo+count-1).sqrt ps)
    (lower : 2≤lo) (index : i<count) :
    (bitsFromList lo count ps).testBit i=true ↔ Nat.Prime (lo+i) := by
  have composite := list_composite_iff certificate lower (by omega : lo≤lo+i)
    (by omega : lo+i≤lo+count-1)
  rw [show lo+i-lo=i by omega] at composite
  rw [bitsFromList,Nat.testBit_ldiff,twoPow_eq,Nat.testBit_two_pow_sub_one]
  simp only [index,decide_true,Bool.true_and]
  cases bit : (compositeFromList lo count ps).testBit i <;> simp_all

theorem bitsFromList_eq {lo count : Nat} {ps : List Nat}
    (certificate : BaseCertificate (lo+count-1).sqrt ps) (lower : 2≤lo) :
    bitsFromList lo count ps=primeBits lo count := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases index : i<count
  · have same := (bitsFromList_prime certificate lower index).trans
      (primeBits_prime lower index).symm
    cases left : (bitsFromList lo count ps).testBit i <;>
      cases right : (primeBits lo count).testBit i <;> simp_all
  · simp [bitsFromList,primeBits,Nat.testBit_ldiff,index]

theorem primitive_eq_list (lo count : Nat) (ps : List Nat) :
    primitiveFromList lo count ps=bitsFromList lo count ps := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [primitiveFromList,bitsFromList,Nat.testBit_xor,Nat.testBit_and,
    Nat.testBit_ldiff]
  cases (twoPow count-1).testBit i <;> cases (compositeFromList lo count ps).testBit i <;> rfl

theorem primitive_eq_original {lo count : Nat} {ps : List Nat}
    (certificate : BaseCertificate (lo+count-1).sqrt ps) (lower : 2≤lo) :
    primitiveFromList lo count ps=primeBits lo count :=
  (primitive_eq_list lo count ps).trans (bitsFromList_eq certificate lower)

#print axioms certified_membership
#print axioms list_composite_iff
#print axioms bitsFromList_eq
#print axioms primitive_eq_original
end RamanujanPV.PackedSievePrimeBase
