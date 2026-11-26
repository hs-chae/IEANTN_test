/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddData
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

/-- Mathematical facts about the actual left cell and actual work+160 product.
Each is preserved by the verified source-data update of every add step. -/
structure AddInvariant (left : Nat) (output work : Nat → Nat) : Prop where
  leftNormalized : NormalizedCell output left
  tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000
  tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1
  leftNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair output (left*12))‖ ≤ 400
  tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair work 160)‖ ≤ 801

/-- Preservation comes from actual pointwise source-output data, including
same-allocation output aliases. No desired intermediate invariant is assumed. -/
theorem add_invariant_after {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4)
    (input table output work : Nat → Nat) (h : AddInvariant (start+j) output work) :
    let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work h.leftNormalized h.tempDigits h.tempSigns
    AddInvariant (start+j) (addOutputData i p output) (addWorkData i p work) := by
  dsimp only
  let p := butterflyAddInput buffers start index step n half j shape split active i
    input table output work h.leftNormalized h.tempDigits h.tempSigns
  have leftWords := add_left_untouched buffers start index step n half j shape split active i
    input table output work h.leftNormalized h.tempDigits h.tempSigns
  have tempWords := add_temp_untouched buffers start index step n half j shape split active i
    input table output work h.leftNormalized h.tempDigits h.tempSigns
  change ∀k,k<12 → addOutputData i p output ((start+j)*12+k)=output ((start+j)*12+k) at leftWords
  change ∀k,k<12 → addWorkData i p work (160+k)=work (160+k) at tempWords
  have leftPair := pair_congr leftWords
  have tempPair := pair_congr tempWords
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · intro c k hk
    have same : addOutputData i p output (12*(start+j)+6*c.val+k)=output (12*(start+j)+6*c.val+k) := by
      simpa [Nat.mul_comm,Nat.add_assoc] using leftWords (6*c.val+k) (by have bound := c.isLt;omega)
    rw [same]
    exact h.leftNormalized.1 c k hk
  · intro c
    have same : addOutputData i p output (12*(start+j)+6*c.val+5)=output (12*(start+j)+6*c.val+5) := by
      simpa [Nat.mul_comm,Nat.add_assoc] using leftWords (6*c.val+5) (by have bound := c.isLt;omega)
    rw [same]
    exact h.leftNormalized.2 c
  · intro c k hk
    have same : addWorkData i p work (160+6*c.val+k)=work (160+6*c.val+k) := by
      simpa only [Nat.add_assoc] using tempWords (6*c.val+k) (by have bound := c.isLt;omega)
    rw [same]
    exact h.tempDigits c k hk
  · intro c
    have same : addWorkData i p work (160+6*c.val+5)=work (160+6*c.val+5) := by
      simpa only [Nat.add_assoc] using tempWords (6*c.val+5) (by have bound := c.isLt;omega)
    rw [same]
    exact h.tempSigns c
  · rw [leftPair]
    exact h.leftNorm
  · rw [tempPair]
    exact h.tempNorm

#print axioms add_invariant_after
end RH080Next.FFTPV.RecursiveSource
