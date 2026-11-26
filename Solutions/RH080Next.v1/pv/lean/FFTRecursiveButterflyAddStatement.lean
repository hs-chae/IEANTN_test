/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddCall
import FFTRecursiveButterflyAddArguments
import FFTRecursiveButterflyAddData
import FFTRecursiveLoopFrame
import FFTRecursiveSegments
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings

/-- Each of the four actual add/status source statements has a total,
all-evaluation-order execution, computed output data and true caller frame.
The C status is proved zero from verified norm bounds. -/
theorem butterfly_add_statement {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner pointerOwner : Nat} {ids : LoopVar → Nat} {pids : PointerVar → Nat}
    {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) (i : Fin 4)
    (leftNormalized : NormalizedCell output (start+j))
    (tempDigits : ∀c : Fin 2,∀k,k<5 → work (160+6*c.val+k)<1000000000)
    (tempSigns : ∀c : Fin 2,work (160+6*c.val+5)≤1)
    (leftNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair output ((start+j)*12))‖ ≤ 400)
    (tempNorm : ‖FFT.IntegerModel.decode (ComplexSource.pair work 160)‖ ≤ 801) :
    let p := butterflyAddInput buffers start index step n half j shape split active i
      input table output work leftNormalized tempDigits tempSigns
    ∃after, NormalSegment context before
        [StatusCall.statement "fixed_add" (butterflyArguments ⟨i.val+1,by omega⟩)] after ∧
      LoopView after buffers start index step n ids owner j input table
        (addOutputData i p output) (addWorkData i p work) ∧
      Locals after pointerName pointerType pids pointerOwner (pointerValue buffers start n half j) ∧
      MultiplyCall.CallerFrame before after [p.layout.object .out] := by
  dsimp only
  let p := butterflyAddInput buffers start index step n half j shape split active i
    input table output work leftNormalized tempDigits tempSigns
  obtain ⟨correct,zero,integerCorrect⟩ := butterfly_add_call context helpers h shape split active i
    leftNormalized tempDigits tempSigns leftNorm tempNorm
  change AddSource.AddCorrect context before p at correct
  change AddSource.rawStatus p=0 at zero
  obtain ⟨⟨after,called,post,oldFrame,everyCall⟩,statusBound,digits,sign,math⟩ := correct
  rw [zero] at called everyCall
  have frame := ComplexSource.add_caller_frame oldFrame
  have writesBuffers : ∀object ∈ [p.layout.object .out],∃r,object=buffers.object r := by
    intro object member
    simp only [List.mem_singleton] at member
    by_cases hi : i.val<2
    · exact ⟨.work,by simpa [p,butterflyAddInput,butterflyAddLayout,hi] using member⟩
    · exact ⟨.output,by simpa [p,butterflyAddInput,butterflyAddLayout,hi] using member⟩
  have inputOutside : buffers.object .input ∉ [p.layout.object .out] := by
    by_cases hi : i.val<2 <;> simp [p,butterflyAddInput,butterflyAddLayout,hi]
  have tableOutside : buffers.object .twiddle ∉ [p.layout.object .out] := by
    by_cases hi : i.val<2 <;> simp [p,butterflyAddInput,butterflyAddLayout,hi]
  have outputAfter : WordArrayRep after (buffers.object .output) (buffers.length .output) (addOutputData i p output) := by
    by_cases hi : i.val<2
    · have preserved := ComplexSource.word_array_after_call h.well (h.arrays .output) frame
        (by simp [p,butterflyAddInput,butterflyAddLayout,hi])
      simpa [addOutputData,hi,bufferData] using preserved
    · simpa [p,butterflyAddInput,butterflyAddLayout,addOutputData,hi] using post
  have workAfter : WordArrayRep after (buffers.object .work) (buffers.length .work) (addWorkData i p work) := by
    by_cases hi : i.val<2
    · simpa [p,butterflyAddInput,butterflyAddLayout,addWorkData,hi] using post
    · have preserved := ComplexSource.word_array_after_call h.well (h.arrays .work) frame
        (by simp [p,butterflyAddInput,butterflyAddLayout,hi])
      simpa [addWorkData,hi,bufferData] using preserved
  have ha := h.after_array_call frame writesBuffers inputOutside tableOutside outputAfter workAfter
  have pa := locals_after_array_call h.well pointers h.arrays frame writesBuffers
  have args : Args context before (butterflyArguments ⟨i.val+1,by omega⟩) (AddSource.arguments p) before := by
    simpa [p,butterflyAddInput,butterflyAddLayout,AddSource.arguments,addValues,addComponent] using
      butterfly_add_arguments context h pointers shape split active i
  have run := StatusCall.assignment_execution (h.bindings.lookup (.inr .status))
    (ha.bindings.lookup (.inr .status)) (h.bindings.slots (.inr .status))
    (ha.bindings.slots (.inr .status)) args called
  refine ⟨after,NormalSegment.single run ?_,ha,pa,frame⟩
  intro other flow otherRun
  apply StatusCall.assignment_every_execution (h.bindings.lookup (.inr .status))
    (ha.bindings.lookup (.inr .status)) (h.bindings.slots (.inr .status))
    (ha.bindings.slots (.inr .status)) _ args everyCall otherRun
  fin_cases i <;> simp [butterflyArguments,SourcePure.CallFree,pointerOffset,addExpr,literal]

#print axioms butterfly_add_statement
end RH080Next.FFTPV.RecursiveSource
