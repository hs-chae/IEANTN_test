/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveContract
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

/-- Returning an actual selected recursive source Call restores the actual
caller's environment and scope by the source function lifetime rule. -/
theorem recursive_call_caller_fields {F : Type} {context : Context F}
    (selected : findFunction context.program "fft_recursive"=some FFTRecursivePV.fft_recursive_ast)
    {before after : State F} {args : List Value}
    (called : Call context "fft_recursive" args before (.value (.integer (integer64 0))) after) :
    after.environment=before.environment ∧ after.scope=before.scope := by
  cases called with
  | external absent named run => rw [selected] at absent;cases absent
  | internal picked shape parameters run converted finished =>
    rw [finished]
    exact ⟨rfl,rfl⟩

/-- The actual leaf Call already satisfies the stronger induction contract,
including normalized output words and both physical allocation footprints. -/
theorem leaf_strong_contract {F : Type} (context : Context F)
    (selected : findFunction context.program "fft_recursive"=some FFTRecursivePV.fft_recursive_ast)
    (copySelected : findFunction context.program "copy_words"=some FFTRecursivePV.copy_words_ast)
    {total : Nat} (buffers : Buffers total) (input table : Nat → Nat) (start index step : Nat)
    (shape : IndexShape start index step 1 total)
    (inputNormalized : ∀k,k<total → NormalizedCell input k) :
    StrongContract context buffers input table 0 start index step := by
  intro before output work well arrays
  have different : buffers.object .output≠buffers.object .input := by
    intro same;have impossible:=buffers.distinct same;cases impossible
  obtain ⟨after,called,outputAfter,inputAfter,frame⟩ := leaf_call context selected copySelected before
    (buffers.object .output) (buffers.length .output) (buffers.object .input) (buffers.length .input)
    (buffers.object .twiddle) (buffers.object .work) start index step total output input well
    (arrays .output) (arrays .input) different shape buffers.outputBound buffers.inputBound
  let data := CopyLoop.prefixData output (fun j=>input (index*12+j)) (start*12) 12
  have newArrays : ∀r,WordArrayRep after (buffers.object r) (buffers.length r)
      (bufferData input table data work r) := by
    intro r
    cases r with
    | output => exact outputAfter
    | input => exact inputAfter
    | twiddle =>
      have old:=well.objectIds _ _ (arrays .twiddle).2.1
      have different : buffers.object .twiddle≠buffers.object .output := by
        intro same;have impossible:=buffers.distinct same;cases impossible
      exact ⟨frame.mode.trans (arrays .twiddle).1,
        (frame.outside _ old (by simpa using different)).trans (arrays .twiddle).2.1,(arrays .twiddle).2.2⟩
    | work =>
      have old:=well.objectIds _ _ (arrays .work).2.1
      have different : buffers.object .work≠buffers.object .output := by
        intro same;have impossible:=buffers.distinct same;cases impossible
      exact ⟨frame.mode.trans (arrays .work).1,
        (frame.outside _ old (by simpa using different)).trans (arrays .work).2.1,(arrays .work).2.2⟩
  have callerFields:=recursive_call_caller_fields selected called
  have callerFrame : MultiplyCall.CallerFrame before after [buffers.object .output,buffers.object .work] := by
    refine ⟨callerFields.1,callerFields.2,frame.well,frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,?_⟩
    intro id old outside
    apply frame.outside id old
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside ⊢
    exact outside.1
  have indexBound : index<total := by have hi:=shape.index;have hp:=shape.stride;omega
  have inputGood:=inputNormalized index indexBound
  have normalized : NormalizedCell data start := by
    apply copy_cell_normalized output input start (index*12)
    · simpa only [Nat.mul_comm] using inputGood.1
    · simpa only [Nat.mul_comm] using inputGood.2
  have post : CallPost buffers 0 start index step input table output work before after data work := by
    refine ⟨newArrays,callerFrame,?_,?_,?_,?_⟩
    · simpa [cells] using copied_leaf_trace (stages table total) output input start index step
    · intro k hk
      have zero : k=0 := by simpa using hk
      subst k
      simpa using normalized
    · intro k hk outside
      have notCopied : ¬(start*12≤k ∧ k<start*12+12) := by simp only [Nat.pow_zero] at outside;omega
      simp [data,CopyLoop.prefixData,notCopied]
    · intro k hk lo hi;rfl
  have bounds:=shape.scalar_bounds
  exact ⟨after,data,work,called,post,fun other result actual=>
    leaf_call_unique selected copySelected well bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.2 called actual⟩

#print axioms leaf_strong_contract
end RH080Next.FFTPV.RecursiveSource
