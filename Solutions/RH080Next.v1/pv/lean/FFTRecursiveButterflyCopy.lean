/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyBirth
import FFTRecursivePointerOffsets
import FFTRecursiveLoopFrame
import FFTRecursiveCopyFrame
import FFTRecursiveHelpers
import FFTRecursiveSegments
import FFTCopyDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings

/-- The actual final twelve-word butterfly copy executes through the proved
C source helper and leaves the entire input work buffer unchanged. -/
theorem butterfly_copy {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner pointerOwner : Nat} {ids : LoopVar → Nat} {pids : PointerVar → Nat}
    {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) :
    ∃after, NormalSegment context before [butterflyCopy] after ∧
      LoopView after buffers start index step n ids owner j input table
        (CopyLoop.prefixData output (fun k => work (48+k)) ((start+j)*12) 12) work ∧
      MultiplyCall.CallerFrame before after [buffers.object .output] := by
  have indices := butterfly_indices shape split active
  have different : buffers.object .output ≠ buffers.object .work := by simp
  have outRange : (start+j)*12+12 ≤ buffers.length .output := by
    have bound := buffers.outputBound;omega
  have workRange : 48+12 ≤ buffers.length .work := by have bound := buffers.workBound;omega
  obtain ⟨after,called,post,source,callerFrame,fullFrame⟩ := CopyLoop.copy_words_call_framed
    context helpers.copy before (buffers.object .output) (buffers.length .output) ((start+j)*12)
    (buffers.object .work) (buffers.length .work) 48 12 output work h.well (h.arrays .output) (h.arrays .work)
    (by intro same;exact False.elim (different same.symm)) (Or.inl different) outRange workRange (by norm_num)
  have frame : MultiplyCall.CallerFrame before after [buffers.object .output] :=
    ⟨callerFrame.environment,callerFrame.scope,fullFrame⟩
  have writesBuffers : ∀object∈[buffers.object .output],∃r,object=buffers.object r := by
    intro object member
    exact ⟨.output,by simpa using member⟩
  have workAfter := ComplexSource.word_array_after_call h.well (h.arrays .work) frame (by simp)
  have ha := h.after_array_call frame writesBuffers (by simp) (by simp) post workAfter
  have evA := Eval.variable (context:=context) (pointers.lookup .a) (pointers.read .a)
  have evWork := Eval.variable (context:=context) (h.bindings.lookup (.inl .work)) (h.bindings.read (.inl .work))
  have offset := word_offset_eval context evWork (h.arrays .work) (offset:=48) (by norm_num)
    (by have bound := buffers.workBound;omega)
  have args : Args context before [.variable "a",pointerOffset "work" 48,literal 12]
      [.pointer (wordPointer (buffers.object .output) ((start+j)*12)),
       .pointer (wordPointer (buffers.object .work) 48),.integer (integer64 12)] before := by
    refine .ordered (List.Perm.refl _) (.cons evA (.cons offset
      (.cons (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl)) .nil))) ?_
    exact .cons rfl (.cons rfl (.cons rfl .nil))
  have run : Exec context before butterflyCopy .normal after := .expression (.call args called)
  have closed : ∀e∈[.variable "a",pointerOffset "work" 48,literal 12],SourcePure.CallFree e := by
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  refine ⟨after,NormalSegment.single run ?_,ha,frame⟩
  intro other flow otherRun
  change Exec context before (.expression (.call "copy_words" [.variable "a",pointerOffset "work" 48,literal 12])) flow other at otherRun
  cases otherRun with
  | expression evaluated =>
    obtain ⟨_,same⟩ := StatusCall.call_eval_unique closed args
      (by intro state result call;exact CopyLoop.call_unique helpers.copy called call) evaluated
    exact ⟨rfl,same⟩
  | callTerminated otherArgs otherCall =>
    obtain ⟨_,middleEq,valuesEq⟩ := ApplicationPureCall.args_unique closed args otherArgs
    rw [middleEq,←valuesEq] at otherCall
    cases (CopyLoop.call_unique helpers.copy called otherCall).1

#print axioms butterfly_copy
end RH080Next.FFTPV.RecursiveSource
