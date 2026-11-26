/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddInput
import ExplicitFFTAddSlice
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

def addOutputData (i : Fin 4) (p : AddSource.Input) (output : Nat → Nat) : Nat → Nat :=
  if i.val<2 then output else AddSource.finalData p

def addWorkData (i : Fin 4) (p : AddSource.Input) (work : Nat → Nat) : Nat → Nat :=
  if i.val<2 then AddSource.finalData p else work

/-- The four actual add operations leave the complete left-child cell intact,
including shared-output-allocation branches. This uses actual computed source
digit data and exact slice boundaries, not an object-frame approximation. -/
theorem add_left_untouched {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4)
    (input table output work : Nat → Nat)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1) :
    let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    ∀k,k<12 → addOutputData i p output ((start+j)*12+k)=output ((start+j)*12+k) := by
  dsimp only
  intro k hk
  by_cases hi : i.val<2
  · simp [addOutputData,hi]
  · let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    have outside : (start+j)*12+k < p.layout.start .out := by
      change (start+j)*12+k < (if i.val<2 then 48+6*(addComponent i).val else (start+j+half)*12+6*(addComponent i).val)
      rw [if_neg hi]
      omega
    have actual := AddSource.finalData_outside p ((start+j)*12+k) (Or.inl outside)
    simpa [addOutputData,p,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual

/-- The verified complex product at work+160 survives every actual add step. -/
theorem add_temp_untouched {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4)
    (input table output work : Nat → Nat)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1) :
    let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    ∀k,k<12 → addWorkData i p work (160+k)=work (160+k) := by
  dsimp only
  intro k hk
  by_cases hi : i.val<2
  · let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    have outside : p.layout.start .out+6 ≤ 160+k := by
      change (if i.val<2 then 48+6*(addComponent i).val else (start+j+half)*12+6*(addComponent i).val)+6 ≤ 160+k
      rw [if_pos hi]
      have c := (addComponent i).isLt
      omega
    have actual := AddSource.finalData_outside p (160+k) (Or.inr outside)
    simpa [addWorkData,p,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual
  · simp [addWorkData,hi]

/-- Equality of actual twelve-word slices preserves their integer model pair. -/
theorem pair_congr {a b : Nat → Nat} {start : Nat}
    (same : ∀k,k<12 → a (start+k)=b (start+k)) : ComplexSource.pair a start = ComplexSource.pair b start := by
  apply Prod.ext
  · apply represented_congr
    intro k hk
    exact same k (by omega)
  · apply represented_congr
    intro k hk
    simpa only [Nat.add_assoc] using same (6+k) (by omega)

#print axioms add_left_untouched
#print axioms add_temp_untouched
end RH080Next.FFTPV.RecursiveSource
