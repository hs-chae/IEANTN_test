/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBufferMap
import FFTRecursiveButterflyIndices
import FFTRecursivePrimitiveBounds
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect WordArrays

/-- Exact complex helper slices in the unchanged butterfly: temp=work+160,
a=the right child cell, b=the stride-selected global twiddle, work=work+0. -/
def butterflyComplexLayout {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) : ComplexSource.Layout where
  object := fun r => match r with
    | .output | .work => buffers.object .work
    | .a => buffers.object .output
    | .b => buffers.object .twiddle
  start := fun r => match r with
    | .output => 160 | .work => 0
    | .a => (start+j+half)*12
    | .b => (j*(total/n))*12
  length := bufferLength buffers
  bound := by
    have indices := butterfly_indices shape split active
    intro r
    cases r <;> simp [bufferLength_object]
    · have h := buffers.workBound;omega
    · have h := buffers.outputBound;omega
    · have h := buffers.twiddleBound;omega
    · have h := buffers.workBound;omega

/-- Input requirements of the actual complex source are derived from real
normalized caller words and source-independent verified norm bounds. -/
def butterflyComplexInput {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half)
    (input table output work : Nat → Nat)
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) : ComplexSource.Input where
  layout := butterflyComplexLayout buffers start index step n half j shape split active
  old := dataByObject buffers input table output work
  disjoint := by
    intro r hr
    cases r
    · exact Or.inr (Or.inr (by norm_num [butterflyComplexLayout]))
    · exact Or.inl (by simp [butterflyComplexLayout])
    · exact Or.inl (by simp [butterflyComplexLayout])
    · exact False.elim (hr rfl)
  digits := by
    intro r hr c k hk
    rcases hr with rfl | rfl
    · simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using rightNormalized.1 c k hk
    · simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using twiddleNormalized.1 c k hk
  signs := by
    intro r hr c
    rcases hr with rfl | rfl
    · simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using rightNormalized.2 c
    · simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using twiddleNormalized.2 c
  magnitude := by
    intro r hr c
    rcases hr with rfl | rfl
    · have h := component_magnitude_of_norm output (start+j+half) 400 rightNorm c
      have hNat : FFT.Limbs.magnitude 1000000000 5
          (fun k => output (12*(start+j+half)+6*c.val+k)) ≤ 400*ComplexSource.unit := by
        norm_num [FFT.IntegerModel.unit] at h
        norm_num [ComplexSource.unit]
        exact_mod_cast h
      have mono : 400*ComplexSource.unit ≤ 1000*ComplexSource.unit := by norm_num [ComplexSource.unit]
      simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using hNat.trans mono
    · have h := component_magnitude_of_norm table (j*(total/n)) 2 twiddleNorm c
      have hNat : FFT.Limbs.magnitude 1000000000 5
          (fun k => table (12*(j*(total/n))+6*c.val+k)) ≤ 2*ComplexSource.unit := by
        norm_num [FFT.IntegerModel.unit] at h
        norm_num [ComplexSource.unit]
        exact_mod_cast h
      have mono : 2*ComplexSource.unit ≤ 1000*ComplexSource.unit := by norm_num [ComplexSource.unit]
      simpa [butterflyComplexLayout,bufferData,Nat.mul_comm] using hNat.trans mono

#print axioms butterflyComplexInput
end RH080Next.FFTPV.RecursiveSource
