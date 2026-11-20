/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSievePrefix

/-! The packed sieve supplies explicitly represented source inputs. Ownership,
scratch allocation and every claim word are proved from the source-owned static
array layout. An unverified physical caller loading these words is not asserted. -/
namespace RamanujanPV.PackedSieveProvider
open QuotientCMachine QuotientDriverInit QuotientCCell SegmentMemory
open PackedSieveKernel PackedSieveSource PackedSieveByteCount PackedSievePrefix
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def inputHeap (lo count : Nat) : Heap :=
  Function.update (initializedHeap canonicalLayout) canonicalLayout.smallBase
    (some {zeroBlock smallArray with words := claims lo count})

theorem input_owned (lo count : Nat) : Owned (inputHeap lo count) := by
  apply owned_of_sameShape (initialized_owned canonicalLayout)
  intro other
  by_cases h : other = canonicalLayout.smallBase
  · subst other
    simp [inputHeap, initialized_small]
  · simp [inputHeap, Function.update_of_ne h]

theorem input_scratch (lo count : Nat) (bound : count ≤ QuotientDriverSource.capacity) :
    SegmentCInit.Buffer (inputHeap lo count) canonicalLayout.largeBase count := by
  refine ⟨zeroBlock largeArray, ?_, bound⟩
  simpa [inputHeap, Function.update_of_ne (Ne.symm canonicalLayout.distinct)] using
    initialized_large canonicalLayout

theorem input_claims (lo count : Nat) (bound : count ≤ QuotientDriverSource.capacity) :
    FlagsRep (inputHeap lo count) canonicalLayout.smallBase count (claims lo count) := by
  intro i hi
  have hb : inputHeap lo count canonicalLayout.smallBase =
      some {zeroBlock smallArray with words := claims lo count} := by simp [inputHeap]
  apply read_of_block hb (by norm_num [canonicalLayout]) (hi.trans_le bound)
    (by norm_num [canonicalLayout, QuotientDriverSource.capacity, modulus] at bound ⊢; omega)
  cases bit : (primeBits lo count).testBit i <;> simp [claims, bit, modulus]

def CountProvider (lo count baseValue : Nat) : Prop :=
  ∀ i, i < count → SourceExecution (lo+i)
    (baseValue + byteCount ((i+8)/8) (prefixBits (i+1) (primeBits lo count)))

theorem source_provider {lo count baseValue : Nat}
    (base : SourceExecution (lo-1) baseValue)
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (storage : count ≤ QuotientDriverSource.capacity) : CountProvider lo count baseValue := by
  let heap := inputHeap lo count
  let s := SegmentCFunctionPrefix.input lo (lo+count-1) count
    canonicalLayout.smallBase canonicalLayout.largeBase heap
  have env := SegmentCFunctionPrefix.input_env lo (lo+count-1) count
    canonicalLayout.smallBase canonicalLayout.largeBase heap
  intro i hi
  exact PackedSievePrefix.source_count_at_byte
    (call := QuotientSqrtExecute.noCalls) (s := s)
    hlo hcount upper (by omega) canonicalLayout.distinct (input_owned lo count)
    (input_scratch lo count storage) (input_claims lo count storage) env base hi

theorem source_bound_provider {lo count baseValue : Nat}
    (base : SourceExecution (lo-1) baseValue)
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (storage : count ≤ QuotientDriverSource.capacity) :
    LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
      SegmentCheckerSource.actualSource SegmentCheckerSource.functions ∧
    CountProvider lo count baseValue :=
  ⟨SegmentCheckerSource.actual_source_checked, source_provider base hlo hcount upper storage⟩

#print axioms input_owned
#print axioms input_scratch
#print axioms input_claims
#print axioms source_provider
#print axioms source_bound_provider
end RamanujanPV.PackedSieveProvider
