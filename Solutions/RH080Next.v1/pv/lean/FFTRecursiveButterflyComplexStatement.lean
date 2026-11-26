/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyComplexCall
import FFTRecursiveButterflyBirth
import FFTRecursiveLoopFrame
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- The actual first arithmetic statement of a butterfly executes the C complex
helper through real pointer/status slots. It proves the integer-model product,
real work-buffer footprint and correctness for every source evaluation order. -/
theorem butterfly_complex_statement {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner pointerOwner : Nat} {ids : LoopVar → Nat} {pids : PointerVar → Nat}
    {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half)
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) :
    ∃after newWork,
      Exec context before (StatusCall.statement "complex_multiply" (butterflyArguments 0)) .normal after ∧
      LoopView after buffers start index step n ids owner j input table output newWork ∧
      Locals after pointerName pointerType pids pointerOwner (pointerValue buffers start n half j) ∧
      ComplexSource.pair newWork 160 = FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n))) ∧
      (∀c : Fin 2,∀k,k<5 → newWork (160+6*c.val+k)<1000000000) ∧
      (∀c : Fin 2,newWork (160+6*c.val+5)≤1) ∧
      (∀k,k<buffers.length .work → (k<160 ∨ 172≤k) → 46≤k → newWork k=work k) ∧
      MultiplyCall.CallerFrame before after [buffers.object .work,buffers.object .work] ∧
      ∀other flow, Exec context before (StatusCall.statement "complex_multiply" (butterflyArguments 0)) flow other →
        flow=.normal ∧ other=after := by
  let p := butterflyComplexInput buffers start index step n half j shape split active
    input table output work rightNormalized twiddleNormalized rightNorm twiddleNorm
  obtain ⟨correct,result⟩ := butterfly_complex_call context helpers h shape split active
    rightNormalized twiddleNormalized rightNorm twiddleNorm
  change ComplexSource.Correct context before p at correct
  change ComplexSource.resultPair p = _ at result
  obtain ⟨after,workData,newWork,called,workOutput,workScratch,pairEq,digits,signs,
    outsideScratch,outsideOutput,frame,everyCall⟩ := correct
  have workAfter : WordArrayRep after (buffers.object .work) (buffers.length .work) newWork := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout] using workOutput
  have frameWork : MultiplyCall.CallerFrame before after [buffers.object .work,buffers.object .work] := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout] using frame
  have writesBuffers : ∀object ∈ [buffers.object .work,buffers.object .work],∃r,object=buffers.object r := by
    intro object member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same <;> exact ⟨.work,same⟩
  have outputAfter := ComplexSource.word_array_after_call h.well (h.arrays .output) frameWork
    (by simp)
  have ha := h.after_array_call frameWork writesBuffers (by simp) (by simp) outputAfter workAfter
  have pa := locals_after_array_call h.well pointers h.arrays frameWork writesBuffers
  have args : Args context before (butterflyArguments 0) (ComplexSource.arguments p) before := by
    change Args context before [.variable "temp",.variable "b",.variable "w",.variable "work"]
      [.pointer (wordPointer (buffers.object .work) 160),
       .pointer (wordPointer (buffers.object .output) ((start+j+half)*12)),
       .pointer (wordPointer (buffers.object .twiddle) ((j*(total/n))*12)),
       .pointer (wordPointer (buffers.object .work) 0)] before
    exact ComplexSource.four_arguments
      (.variable (h.bindings.lookup (.inr .temp)) (h.bindings.read (.inr .temp)))
      (.variable (pointers.lookup .b) (pointers.read .b))
      (.variable (pointers.lookup .w) (pointers.read .w))
      (.variable (h.bindings.lookup (.inl .work)) (h.bindings.read (.inl .work)))
  have run := StatusCall.assignment_execution (h.bindings.lookup (.inr .status))
    (ha.bindings.lookup (.inr .status)) (h.bindings.slots (.inr .status))
    (ha.bindings.slots (.inr .status)) args called
  have product : ComplexSource.pair newWork 160 =
      FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n))) := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout] using pairEq.trans result
  have normalized : (∀c : Fin 2,∀k,k<5 → newWork (160+6*c.val+k)<1000000000) := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout] using digits
  have signed : (∀c : Fin 2,newWork (160+6*c.val+5)≤1) := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout] using signs
  have outside : ∀k,k<buffers.length .work → (k<160 ∨ 172≤k) → 46≤k → newWork k=work k := by
    simpa [p,butterflyComplexInput,butterflyComplexLayout,bufferData] using outsideOutput
  refine ⟨after,newWork,run,ha,pa,product,normalized,signed,outside,frameWork,?_⟩
  intro other flow otherRun
  apply StatusCall.assignment_every_execution (h.bindings.lookup (.inr .status))
    (ha.bindings.lookup (.inr .status)) (h.bindings.slots (.inr .status))
    (ha.bindings.slots (.inr .status)) _ args everyCall otherRun
  intro e member
  change e ∈ [.variable "temp",.variable "b",.variable "w",.variable "work"] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> trivial

#print axioms butterfly_complex_statement
end RH080Next.FFTPV.RecursiveSource
