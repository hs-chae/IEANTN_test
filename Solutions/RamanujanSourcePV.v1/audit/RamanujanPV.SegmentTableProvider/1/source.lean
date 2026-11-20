/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentTableAdapter
import RamanujanPV.SegmentNetwork
import RamanujanPV.SegmentWindowCells

/-! Source-derived numerical providers for the existing network cells. The
certificate input words are represented explicitly; Owned, allocation extents
and all scratch initialization are proved, not trusted application platform
facts. No assertion is made about an unverified physical caller loading them. -/
namespace RamanujanPV.SegmentTableProvider
open QuotientCMachine QuotientDriverInit QuotientCCell
open SegmentMemory SegmentCheckerMath SegmentTableAdapter WindowCells
open QuotientDemandCheck PrimeWindow SegmentWindowCells
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Only the arithmetic cumulative-field check is used here. In particular,
this lemma invokes no prime-count/cardinality theorem. -/
theorem sum_flags_offset {base count primeCount offset : Nat} {primes : Lean.RArray Nat}
    {entries : Lean.RArray PrimeWindow.Entry}
    (checked : checkAll base primes primeCount entries count=true) (bound : offset ≤ count) :
    (∑i∈Finset.range offset,flags entries i)=offsetValue entries offset := by
  induction offset with
  | zero => simp [offsetValue]
  | succ offset ih =>
    have prior := ih (by omega)
    have entry := allFrom_at count 0 checked offset (by omega) (by omega)
    have clauses :
        (if (entries.get offset).isPrime then
          decide ((entries.get offset).witness < primeCount ∧ primes.get (entries.get offset).witness=base+offset+1)
        else decide (2 ≤ (entries.get offset).witness ∧ (entries.get offset).witness < base+offset+1 ∧
          (base+offset+1)%(entries.get offset).witness=0))=true ∧
        (entries.get offset).cumulative=(if offset=0 then 0 else (entries.get (offset-1)).cumulative)+
          (if (entries.get offset).isPrime then 1 else 0) := by
      simpa [checkEntry] using entry
    rw [Finset.sum_range_succ,prior]
    simpa [offsetValue,flags] using clauses.2.symm

/-- Concrete representation of input certificate bytes. The two source-owned
static-array extents are reused only as valid storage layout. Replacement of
input words here specifies the function input; it is not a claimed C loader. -/
noncomputable def inputHeap (entries : Lean.RArray PrimeWindow.Entry) : Heap :=
  Function.update (initializedHeap canonicalLayout) canonicalLayout.smallBase
    (some {zeroBlock smallArray with words:=flags entries})

theorem input_owned (entries : Lean.RArray PrimeWindow.Entry) : Owned (inputHeap entries) := by
  apply owned_of_sameShape (initialized_owned canonicalLayout)
  intro other
  by_cases h : other=canonicalLayout.smallBase
  · subst other
    simp [inputHeap,initialized_small]
  · simp [inputHeap,Function.update_of_ne h]

theorem input_scratch (entries : Lean.RArray PrimeWindow.Entry) {count : Nat}
    (bound : count ≤ QuotientDriverSource.capacity) :
    SegmentCInit.Buffer (inputHeap entries) canonicalLayout.largeBase count := by
  refine ⟨zeroBlock largeArray,?_,bound⟩
  simpa [inputHeap,Function.update_of_ne (Ne.symm canonicalLayout.distinct)] using
    initialized_large canonicalLayout

theorem input_claims (entries : Lean.RArray PrimeWindow.Entry) {count : Nat}
    (bound : count ≤ QuotientDriverSource.capacity) :
    FlagsRep (inputHeap entries) canonicalLayout.smallBase count (flags entries) := by
  intro i hi
  have hb : inputHeap entries canonicalLayout.smallBase=
      some {zeroBlock smallArray with words:=flags entries} := by simp [inputHeap]
  apply read_of_block hb (by norm_num [canonicalLayout]) (by exact hi.trans_le bound)
    (by norm_num [canonicalLayout,QuotientDriverSource.capacity] at bound ⊢; omega)
  cases hp : (entries.get i).isPrime  < ;> simp [flags,hp,modulus]

/-- Every count consumed below comes from the accepted actual segmented source
execution via positive_output_sound. Local certificate use here establishes the
source's successful comparison branch, not prime counts by a parallel shortcut. -/
theorem source_provider {base count value primeCount : Nat} {primes : Lean.RArray Nat}
    {entries : Lean.RArray PrimeWindow.Entry}
    (baseRun : SourceExecution base value)
    (primeGood : ∀j,j < primeCount → Nat.Prime (primes.get j))
    (checked : checkAll base primes primeCount entries count=true)
    (basePositive : 1 ≤ base) (countPositive : 0 < count)
    (upper : base+count ≤ 2000000000000) (storage : count ≤ QuotientDriverSource.capacity) :
    CountProvider base count value entries := by
  let heap := inputHeap entries
  let s := SegmentCFunctionPrefix.input (base+1) (base+count) count
    canonicalLayout.smallBase canonicalLayout.largeBase heap
  have length : base+count-(base+1)+1=count := by omega
  have env := SegmentCFunctionPrefix.input_env (base+1) (base+count) count
    canonicalLayout.smallBase canonicalLayout.largeBase heap
  have owned : Owned heap := input_owned entries
  have scratch := input_scratch entries storage
  have claims := input_claims entries storage
  obtain ⟨t,run,envt,ownedt⟩ := SegmentCFunction.correct_claims_execution
    (call:=QuotientSqrtExecute.noCalls) (s:=s) (by omega : 2 ≤ base+1) (by omega) upper
    (by omega) canonicalLayout.distinct owned (by simpa [length] using scratch)
    (by simpa [length] using claims) env
    (classified_flags primeGood checked basePositive countPositive)
  have outputWord : segmentCount (base+1) (base+count)+1 < modulus := by
    have bound := SegmentCounts.sum_finalFlags_le (lo:=base+1) (hi:=base+count)
      (by omega) (by omega)
    rw [SegmentCounts.sum_finalFlags (by omega) (by omega),length] at bound
    norm_num [modulus]
    omega
  intro offset offsetBound
  by_cases zero : offset=0
  · subst offset
    simpa [offsetValue] using baseRun
  · have index : offset-1 < count := by omega
    have actualBase : SourceExecution (base+1-1) value := by simpa using baseRun
    have out := SegmentNetwork.source_count_at (s:=s) (t:=t) (i:=offset-1)
      (by omega : 2 ≤ base+1) (by omega) upper (by omega) canonicalLayout.distinct owned
      (by simpa [length] using scratch) (by simpa [length] using claims) env run
      (uint64_of_u64 outputWord) (by omega) actualBase (by omega)
    have next : base+1+(offset-1)=base+offset := by omega
    have successor : offset-1+1=offset := by omega
    rw [next,successor,sum_flags_offset checked offsetBound] at out
    exact out

#print axioms sum_flags_offset
#print axioms input_owned
#print axioms source_provider
end RamanujanPV.SegmentTableProvider
