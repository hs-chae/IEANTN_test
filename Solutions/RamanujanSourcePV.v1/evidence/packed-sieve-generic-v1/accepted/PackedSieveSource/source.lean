/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveCorrect
import RamanujanPV.PackedSieveByteWidth
import RamanujanPV.SegmentNetwork

/-! The proved packed sieve supplies the input claims of the complete actual C
segmented checker. Every source count below passes through that actual source
execution and its soundness theorem. Physical argument loading, a native
packed-bitset implementation, and a physical execution receipt are not asserted. -/
namespace RamanujanPV.PackedSieveSource
open Finset PackedSieveKernel PackedSieveCorrect PackedSieveByteCount
open PackedSieveByteWidth SegmentCheckerMath QuotientCMachine SegmentMemory QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 0

def claims (lo count i : Nat) : Nat := if (primeBits lo count).testBit i then 1 else 0

theorem classified_claims {lo count i : Nat} (hlo : 2 ≤ lo) (hi : i < count) :
    claims lo count i = finalFlags lo (lo+count-1) i := by
  rw [final_flag hlo (by omega)]
  have correct := primeBits_prime hlo hi
  cases bit : (primeBits lo count).testBit i
  · have composite : ¬Nat.Prime (lo+i) := by
      intro prime
      have := correct.mpr prime
      rw [bit] at this
      contradiction
    simp [claims, bit, composite]
  · have prime := correct.mp bit
    simp [claims, bit, prime]

theorem byteCount_eq_segmentCount {lo count : Nat} (hlo : 2 ≤ lo) (hcount : 0 < count) :
    byteCount ((count+7)/8) (primeBits lo count) = segmentCount lo (lo+count-1) := by
  rw [byteCount_ceil_width]
  have length : lo+count-1-lo+1 = count := by omega
  calc
    lowCount count (primeBits lo count) =
        ∑ i ∈ range count, finalFlags lo (lo+count-1) i := by
      apply sum_congr rfl
      intro i hi
      exact classified_claims hlo (mem_range.mp hi)
    _ = segmentCount lo (lo+count-1) := by
      simpa only [length] using SegmentCounts.sum_finalFlags hlo (by omega : lo ≤ lo+count-1)

theorem primeCounting_increment {lo count : Nat} (hlo : 2 ≤ lo) (hcount : 0 < count) :
    Nat.primeCounting (lo+count-1) = Nat.primeCounting (lo-1) +
      byteCount ((count+7)/8) (primeBits lo count) := by
  rw [byteCount_eq_segmentCount hlo hcount]
  exact SegmentCheckerMath.primeCounting_increment hlo (by omega)

theorem source_execution {call : Service} {s : State}
    {lo count capacity cb fb : Nat}
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (cap : count ≤ capacity) (apart : cb ≠ fb)
    (owned : Owned s.heap) (scratch : SegmentCInit.Buffer s.heap fb count)
    (inputFlags : FlagsRep s.heap cb count (claims lo count))
    (env : SegmentCFunctionPrefix.Inputs lo (lo+count-1) capacity cb fb s.env) :
    ∃ t, Run call SegmentCheckerSource.checkerFunction.body s
        (.returned t (.u64 (byteCount ((count+7)/8) (primeBits lo count)+1))) ∧
      t.env = s.env ∧ Owned t.heap := by
  have length : lo+count-1-lo+1 = count := by omega
  obtain ⟨t, run, envt, ownedt⟩ := SegmentCFunction.correct_claims_execution
    (call := call) hlo (by omega) upper (by omega) apart owned
    (by simpa only [length] using scratch) (by simpa only [length] using inputFlags) env
    (by intro i hi; exact classified_claims hlo (by omega))
  exact ⟨t, by simpa only [byteCount_eq_segmentCount hlo hcount] using run, envt, ownedt⟩

theorem source_count_at {call : Service} {s : State}
    {lo count capacity cb fb baseValue i : Nat}
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (cap : count ≤ capacity) (apart : cb ≠ fb)
    (owned : Owned s.heap) (scratch : SegmentCInit.Buffer s.heap fb count)
    (inputFlags : FlagsRep s.heap cb count (claims lo count))
    (env : SegmentCFunctionPrefix.Inputs lo (lo+count-1) capacity cb fb s.env)
    (base : SourceExecution (lo-1) baseValue) (index : i < count) :
    SourceExecution (lo+i) (baseValue+lowCount (i+1) (primeBits lo count)) := by
  obtain ⟨t, run, _, _⟩ := source_execution
    (call := call) hlo hcount upper cap apart owned scratch inputFlags env
  have length : lo+count-1-lo+1 = count := by omega
  have word : byteCount ((count+7)/8) (primeBits lo count)+1 < modulus := by
    rw [byteCount_eq_segmentCount hlo hcount]
    have bound := SegmentCounts.sum_finalFlags_le hlo (by omega : lo ≤ lo+count-1)
    rw [SegmentCounts.sum_finalFlags hlo (by omega), length] at bound
    norm_num [modulus]
    omega
  have actual := SegmentNetwork.source_count_at
    hlo (by omega) upper (by omega) apart owned
    (by simpa only [length] using scratch) (by simpa only [length] using inputFlags)
    env run (uint64_of_u64 word) (by omega) base (by omega : i < lo+count-1-lo+1)
  exact actual

/-- Explicit source-byte association is packaged with the numerical source
consumer; the same AST supplies the count above and renders this exact C text. -/
theorem source_bound_count_at {call : Service} {s : State}
    {lo count capacity cb fb baseValue i : Nat}
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (cap : count ≤ capacity) (apart : cb ≠ fb)
    (owned : Owned s.heap) (scratch : SegmentCInit.Buffer s.heap fb count)
    (inputFlags : FlagsRep s.heap cb count (claims lo count))
    (env : SegmentCFunctionPrefix.Inputs lo (lo+count-1) capacity cb fb s.env)
    (base : SourceExecution (lo-1) baseValue) (index : i < count) :
    LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
      SegmentCheckerSource.actualSource SegmentCheckerSource.functions ∧
    SourceExecution (lo+i) (baseValue+lowCount (i+1) (primeBits lo count)) :=
  ⟨SegmentCheckerSource.actual_source_checked,
   source_count_at (call := call) hlo hcount upper cap apart owned scratch inputFlags env base index⟩

#print axioms classified_claims
#print axioms byteCount_eq_segmentCount
#print axioms primeCounting_increment
#print axioms source_execution
#print axioms source_count_at
#print axioms source_bound_count_at
end RamanujanPV.PackedSieveSource
