/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBufferMap
import FFTRecursiveButterflyIndices
import FFTRecursivePairBounds
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

def addComponent (i : Fin 4) : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by norm_num)⟩

def butterflyAddLayout {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4) : AddSource.Layout where
  object := fun r => match r with
    | .out => if i.val<2 then buffers.object .work else buffers.object .output
    | .a => buffers.object .output | .b => buffers.object .work
  start := fun r => match r with
    | .out => if i.val<2 then 48+6*(addComponent i).val else (start+j+half)*12+6*(addComponent i).val
    | .a => (start+j)*12+6*(addComponent i).val
    | .b => 160+6*(addComponent i).val
  length := bufferLength buffers
  bound := by
    have indices := butterfly_indices shape split active
    have component := (addComponent i).isLt
    intro r
    cases r
    · split_ifs <;> simp only [bufferLength_object]
      · have h := buffers.workBound;omega
      · have h := buffers.outputBound;omega
    · simp only [bufferLength_object]
      have h := buffers.outputBound;omega
    · simp only [bufferLength_object]
      have h := buffers.workBound;omega
  safeA := by
    have component := (addComponent i).isLt
    unfold AddSource.SafeAlias
    split_ifs
    · exact Or.inl (by simp)
    · refine Or.inr (Or.inr (Or.inr ?_))
      change (start+j)*12+6*(addComponent i).val+6 ≤ (start+j+half)*12+6*(addComponent i).val
      omega
  safeB := by
    have component := (addComponent i).isLt
    unfold AddSource.SafeAlias
    split_ifs
    · refine Or.inr (Or.inr (Or.inl ?_))
      change 48+6*(addComponent i).val+6 ≤ 160+6*(addComponent i).val
      omega
    · exact Or.inl (by simp)

/-- Real normalized source operands determine each of the four actual add
inputs, including all aliases and exact output/scratch slice boundaries. -/
def butterflyAddInput {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4)
    (input table output work : Nat → Nat)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1) : AddSource.Input where
  layout := butterflyAddLayout buffers start index step n half j shape split active i
  old := dataByObject buffers input table output work
  subtract := if i.val<2 then 0 else 1
  subtract_bound := by split_ifs <;> decide
  digitsA := by
    intro k hk
    simpa [butterflyAddLayout,bufferData,IncrementSource.base,Nat.mul_comm] using leftNormalized.1 (addComponent i) k hk
  digitsB := by
    intro k hk
    simpa [butterflyAddLayout,bufferData,IncrementSource.base] using tempDigits (addComponent i) k hk
  signA := by
    simpa [butterflyAddLayout,bufferData,Nat.mul_comm] using leftNormalized.2 (addComponent i)
  signB := by
    simpa [butterflyAddLayout,bufferData] using tempSigns (addComponent i)

/-- Overflow freedom is proved from child/product norm bounds, rather than
assumed as an intended successful numerical execution. -/
theorem butterfly_add_status_zero {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (i : Fin 4)
    (input table output work : Nat → Nat)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1)
    (leftNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair output ((start+j)*12))‖ ≤ 400)
    (tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair work 160)‖ ≤ 801) :
    AddSource.rawStatus (butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns) = 0 := by
  let p := butterflyAddInput buffers start index step n half j shape split active i
    input table output work leftNormalized tempDigits tempSigns
  change AddSource.rawStatus p=0
  have ha : AddSource.Input.a p = (fun k => output ((start+j)*12+6*(addComponent i).val+k)) := by
    funext k
    simp [p,AddSource.Input.a,butterflyAddInput,butterflyAddLayout,bufferData]
  have hb : AddSource.Input.b p = (fun k => work (160+6*(addComponent i).val+k)) := by
    funext k
    simp [p,AddSource.Input.b,butterflyAddInput,butterflyAddLayout,bufferData]
  apply AddSource.rawStatus_zero_of_sum_lt p
  rw [ha,hb]
  exact butterfly_add_capacity output work ((start+j)*12) leftNorm tempNorm (addComponent i)

#print axioms butterfly_add_status_zero
end RH080Next.FFTPV.RecursiveSource
