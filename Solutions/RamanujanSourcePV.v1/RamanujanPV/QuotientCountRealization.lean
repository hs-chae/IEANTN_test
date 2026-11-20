/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCCell
import RamanujanPV.QuotientDriverInit

/-! Numerical kernel proofs and verified C source are distinct components.
This file combines a supplied exact count theorem with the separately verified
actual C program, actual helper realization, and source-owned zero-initialized
buffers. It does not label the numerical certificate alone as PV, nor assert a
physical native process/stdout correspondence. -/
namespace RamanujanPV.QuotientCountRealization
open QuotientCMachine QuotientDriverInit QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Any exact supported prime-count value is realized by the actual verified
source function. The canonical buffers are constructed from the actual static
array source declarations, not assumed to contain the intended count tables. -/
theorem source_execution_from_kernel_value {N output : Nat}
    (hN2 : 2 ≤ N) (hN : N ≤ 2000000000000)
    (value : Nat.primeCounting N=output) : SourceExecution N output := by
  let layout := canonicalLayout
  have capWord : QuotientDriverSource.capacity < modulus := by
    norm_num [QuotientDriverSource.capacity,modulus]
  have rootCapacity : N.sqrt < QuotientDriverSource.capacity := by
    rw [Nat.sqrt_lt]
    norm_num [QuotientDriverSource.capacity]
    omega
  have buffers : QuotientCInit.Buffers (initializedHeap layout)
      layout.smallBase layout.largeBase N.sqrt := by
    refine ⟨layout.distinct,zeroBlock smallArray,zeroBlock largeArray,
      initialized_small layout,initialized_large layout,?_,?_⟩
    · exact rootCapacity
    · exact rootCapacity
  obtain ⟨t,run,envt,ownedt⟩ := QuotientCFunction.linked_function_refines
    N QuotientDriverSource.capacity layout.smallBase layout.largeBase
    (initializedHeap layout) hN2 hN rootCapacity capWord (initialized_owned layout) buffers
  refine ⟨QuotientDriverSource.capacity,layout.smallBase,layout.largeBase,
    initializedHeap layout,t,hN2,hN,rootCapacity,capWord,initialized_owned layout,buffers,?_⟩
  simpa only [value] using run

#print axioms source_execution_from_kernel_value
end RamanujanPV.QuotientCountRealization
