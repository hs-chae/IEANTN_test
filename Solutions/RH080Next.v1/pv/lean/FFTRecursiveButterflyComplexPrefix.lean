/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyComplexStatement
import FFTRecursiveSegments
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Actual four-statement source prefix: three real pointer declarations and
the real C complex/status statement. This includes all permitted executions,
with no assumed initialized pointer locals, scratch buffer or desired output. -/
theorem butterfly_complex_prefix {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner : Nat} {ids : LoopVar → Nat}
    {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half)
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) :
    ∃after newWork,
      NormalSegment context before (butterflyStatements.take 4) after ∧
      LoopView after buffers start index step n ids owner j input table output newWork ∧
      Locals after pointerName pointerType (pointerIds before.nextObject) before.scope (pointerValue buffers start n half j) ∧
      ComplexSource.pair newWork 160 = FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n))) ∧
      (∀c : Fin 2,∀k,k<5 → newWork (160+6*c.val+k)<1000000000) ∧
      (∀c : Fin 2,newWork (160+6*c.val+5)≤1) ∧
      (∀k,k<buffers.length .work → (k<160 ∨ 172≤k) → 46≤k → newWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .work] := by
  obtain ⟨initialized,born,hi,pointers,birthFrame⟩ := butterfly_pointer_births context h shape split active
  obtain ⟨after,newWork,run,ha,pa,product,digits,signs,outside,callFrame,every⟩ :=
    butterfly_complex_statement context helpers hi pointers shape split active
      rightNormalized twiddleNormalized rightNorm twiddleNorm
  have declarations : NormalSegment context before (butterflyStatements.take 3) initialized := by
    apply NormalSegment.pure born
    intro s member
    change s ∈ [.declare (.pointer .u64) "a" (some butterflyA),
      .declare (.pointer .u64) "b" (some butterflyB),.declare (.pointer .u64) "w" (some butterflyW)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  have arithmetic := NormalSegment.single run every
  have all : NormalSegment context before (butterflyStatements.take 4) after := by
    simpa [butterflyStatements] using declarations.append arithmetic
  have birthWork : Frame before.nextObject before initialized [buffers.object .work] :=
    ⟨birthFrame.well,birthFrame.fresh,birthFrame.nextObject,birthFrame.nextScope,birthFrame.mode,birthFrame.foreign,
      fun id old _ => birthFrame.outside id old (by simp)⟩
  have arithmeticWork : Frame before.nextObject initialized after [buffers.object .work] := by
    refine ⟨callFrame.frame.well,birthFrame.fresh.trans callFrame.frame.fresh,
      callFrame.frame.nextObject,callFrame.frame.nextScope,callFrame.frame.mode,callFrame.frame.foreign,?_⟩
    intro id old absent
    exact callFrame.frame.outside id (old.trans_le birthFrame.nextObject) (by simpa using absent)
  exact ⟨after,newWork,all,ha,pa,product,digits,signs,outside,birthWork.trans arithmeticWork⟩

#print axioms butterfly_complex_prefix
end RH080Next.FFTPV.RecursiveSource
