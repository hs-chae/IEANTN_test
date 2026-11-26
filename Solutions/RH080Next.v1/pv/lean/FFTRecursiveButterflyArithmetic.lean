/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyComplexPrefix
import FFTRecursiveButterflyFourAdds
import FFTRecursiveButterflyPairs
import FFTRecursiveButterflyAddFootprint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

/-- All eight arithmetic/pointer source instructions have genuine all-order
execution and compute the complex butterfly sum/difference. Every raw word
outside their actual output/work slices is preserved. -/
theorem butterfly_arithmetic {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner : Nat} {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half)
    (leftNormalized : NormalizedCell output (start+j))
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (leftNorm : ‖FFT.IntegerModel.decode (cell output (start+j))‖ ≤ 400)
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) :
    ∃after newOutput newWork,
      NormalSegment context before (butterflyStatements.take 8) after ∧
      LoopView after buffers start index step n ids owner j input table newOutput newWork ∧
      Locals after pointerName pointerType (pointerIds before.nextObject) before.scope (pointerValue buffers start n half j) ∧
      ComplexSource.pair newWork 48 = FFT.IntegerModel.add (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      cell newOutput (start+j+half) = FFT.IntegerModel.sub (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      (∀c : Fin 2,∀k,k<5 → newWork (48+6*c.val+k)<1000000000) ∧
      (∀c : Fin 2,newWork (48+6*c.val+5)≤1) ∧ NormalizedCell newOutput (start+j+half) ∧
      (∀k,(k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → newOutput k=output k) ∧
      (∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → newWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work] := by
  obtain ⟨middle,temp,complex,hm,pm,product,tempDigits,tempSigns,tempOutside,complexFrame⟩ :=
    butterfly_complex_prefix context helpers h shape split active rightNormalized twiddleNormalized rightNorm twiddleNorm
  have tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair temp 160)‖ ≤ 801 := by
    rw [product]
    exact FFT.IntegerModel.decoded_product_norm_le_801 _ _ rightNorm twiddleNorm
  let world : AddWorld (start+j) := ⟨output,temp,leftNormalized,tempDigits,tempSigns,
    by simpa [cell,ComplexSource.pair,Nat.mul_comm] using leftNorm,tempNorm⟩
  let last := addWorldFour buffers start index step n half j shape split active input table world
  obtain ⟨after,adds,ha,pa,addFrame⟩ := four_adds_execution context helpers world hm pm shape split active
  change LoopView after buffers start index step n ids owner j input table last.output last.work at ha
  have whole : NormalSegment context before (butterflyStatements.take 8) after := by
    simpa [butterflyStatements] using complex.append adds
  have pairs := four_add_pairs buffers start index step n half j shape split active input table world
  have normalized := four_add_pairs_normalized buffers start index step n half j shape split active input table world
  have footprint := four_add_footprint buffers start index step n half j shape split active input table world
  change ComplexSource.pair last.work 48 = _ ∧ ComplexSource.pair last.output ((start+j+half)*12) = _ at pairs
  have first : ComplexSource.pair last.work 48 = FFT.IntegerModel.add (cell output (start+j))
      (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) := by
    have original : ComplexSource.pair last.work 48 = FFT.IntegerModel.add
        (ComplexSource.pair output ((start+j)*12)) (ComplexSource.pair temp 160) := pairs.1
    rw [product] at original
    simpa [cell,ComplexSource.pair,Nat.mul_comm] using original
  have second : cell last.output (start+j+half) = FFT.IntegerModel.sub (cell output (start+j))
      (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) := by
    have original : ComplexSource.pair last.output ((start+j+half)*12) = FFT.IntegerModel.sub
        (ComplexSource.pair output ((start+j)*12)) (ComplexSource.pair temp 160) := pairs.2
    rw [product] at original
    simpa [cell,ComplexSource.pair,Nat.mul_comm] using original
  have outputOutside : ∀k,(k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → last.output k=output k := footprint.1
  have workOutside : ∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → last.work k=work k := by
    intro k hk high outside
    exact (footprint.2 k (Or.inr high)).trans (tempOutside k hk outside (by omega))
  have firstFrame : Frame before.nextObject before middle [buffers.object .output,buffers.object .work] := by
    refine ⟨complexFrame.well,complexFrame.fresh,complexFrame.nextObject,complexFrame.nextScope,
      complexFrame.mode,complexFrame.foreign,?_⟩
    intro id old absent
    apply complexFrame.outside id old
    simpa only [List.mem_singleton] using fun same => absent (by simp [same])
  have secondFrame : Frame before.nextObject middle after [buffers.object .output,buffers.object .work] := by
    refine ⟨addFrame.well,complexFrame.fresh.trans addFrame.fresh,addFrame.nextObject,
      addFrame.nextScope,addFrame.mode,addFrame.foreign,?_⟩
    intro id old absent
    exact addFrame.outside id (old.trans_le complexFrame.nextObject) absent
  exact ⟨after,last.output,last.work,whole,ha,pa,first,second,normalized.1,normalized.2.1,
    normalized.2.2,outputOutside,workOutside,firstFrame.trans secondFrame⟩

#print axioms butterfly_arithmetic
end RH080Next.FFTPV.RecursiveSource
