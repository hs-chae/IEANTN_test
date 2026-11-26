/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyArithmetic
import FFTRecursiveButterflyCopy
import FFTRecursiveButterflyCopyData
import FFTRecursiveLoopControl
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

/-- Actual entire ten-statement source butterfly contents, including three
pointer births, all five numerical calls, copy12 and j increment. Totality,
every execution order, both exact model outputs, normalization and actual
word footprints are all established from the original caller words. -/
theorem butterfly_contents {F : Type} (context : Context F) (helpers : Helpers context)
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
      NormalSegment context before butterflyStatements after ∧
      LoopView after buffers start index step n ids owner (j+1) input table newOutput newWork ∧
      cell newOutput (start+j) = FFT.IntegerModel.add (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      cell newOutput (start+j+half) = FFT.IntegerModel.sub (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      NormalizedCell newOutput (start+j) ∧ NormalizedCell newOutput (start+j+half) ∧
      (∀k,(k<(start+j)*12 ∨ (start+j)*12+12≤k) →
        (k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → newOutput k=output k) ∧
      (∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → newWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
  obtain ⟨middle,out8,work8,arithmetic,hm,pm,sum,difference,sumDigits,sumSigns,rightNormalized8,
    outOutside,workOutside,arithFrame⟩ := butterfly_arithmetic context helpers h shape split active
      leftNormalized rightNormalized twiddleNormalized leftNorm rightNorm twiddleNorm
  obtain ⟨copied,copy,hc,copyFrame⟩ := butterfly_copy context helpers hm pm shape split active
  have active' : j<n/2 := by omega
  obtain ⟨after,increment,ha,incrementFrame⟩ := loop_increment context hc shape active'
  let result := CopyLoop.prefixData out8 (fun k => work8 (48+k)) ((start+j)*12) 12
  change LoopView after buffers start index step n ids owner (j+1) input table result work8 at ha
  have whole : NormalSegment context before butterflyStatements after := by
    simpa [butterflyStatements] using (arithmetic.append copy).append increment
  have leftEq : cell result (start+j) = FFT.IntegerModel.add (cell output (start+j))
      (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) := by
    have copiedModel := cell_copy_leaf out8 work8 (start+j) 4
    have exactCopy : cell result (start+j) = ComplexSource.pair work8 48 := by
      simpa [result,cell,ComplexSource.pair] using copiedModel
    exact exactCopy.trans sum
  have different : start+j+half≠start+j := by omega
  have rightEq : cell result (start+j+half) = FFT.IntegerModel.sub (cell output (start+j))
      (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) :=
    (copy_cell_other out8 work8 (start+j) 48 (start+j+half) different).trans difference
  have leftGood : NormalizedCell result (start+j) := copy_cell_normalized out8 work8 (start+j) 48 sumDigits sumSigns
  have rightGood : NormalizedCell result (start+j+half) := copy_other_normalized out8 work8 (start+j) 48
    (start+j+half) different rightNormalized8
  have outside : ∀k,(k<(start+j)*12 ∨ (start+j)*12+12≤k) →
      (k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → result k=output k := by
    intro k outsideLeft outsideRight
    have notCopied : ¬((start+j)*12≤k ∧ k<(start+j)*12+12) := by omega
    change (if (start+j)*12≤k ∧ k<(start+j)*12+12 then _ else out8 k) = _
    rw [if_neg notCopied]
    exact outOutside k outsideRight
  have f1 : Frame before.nextObject before middle [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
    refine ⟨arithFrame.well,arithFrame.fresh,arithFrame.nextObject,arithFrame.nextScope,
      arithFrame.mode,arithFrame.foreign,?_⟩
    intro id old absent
    apply arithFrame.outside id old
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at absent
    simp [absent.1,absent.2.1]
  have f2 : Frame before.nextObject middle copied [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
    refine ⟨copyFrame.frame.well,arithFrame.fresh.trans copyFrame.frame.fresh,copyFrame.frame.nextObject,
      copyFrame.frame.nextScope,copyFrame.frame.mode,copyFrame.frame.foreign,?_⟩
    intro id old absent
    apply copyFrame.frame.outside id (old.trans_le arithFrame.nextObject)
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at absent
    simpa only [List.mem_singleton] using absent.1
  have f3 : Frame before.nextObject copied after [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
    refine ⟨incrementFrame.well,f2.fresh.trans incrementFrame.fresh,incrementFrame.nextObject,
      incrementFrame.nextScope,incrementFrame.mode,incrementFrame.foreign,?_⟩
    intro id old absent
    apply incrementFrame.outside id (old.trans_le (arithFrame.nextObject.trans copyFrame.frame.nextObject))
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at absent
    simpa only [List.mem_singleton] using absent.2.2
  exact ⟨after,result,work8,whole,ha,leftEq,rightEq,leftGood,rightGood,outside,workOutside,(f1.trans f2).trans f3⟩

#print axioms butterfly_contents
end RH080Next.FFTPV.RecursiveSource
