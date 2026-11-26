/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainParameter
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Only generic allocator/deallocator behavior, not successful allocation,
initialized application state, intended launches or correct program outputs. -/
def MemorySound {F : Type} (context : Context F) : Prop :=
  ∀operation args before result after,operation=.calloc ∨ operation=.free →
    context.foreign (.call operation) args before result after →
    ∃value,result=.value value ∧ PlatformMemory.Call F operation args before value after

/-- A concrete execution context for the norm functions. Their calls to calloc
and free follow exactly the selected generic API model. printf is a separate
I/O contract for main; it is not invoked by the norm function itself. -/
def memoryContext (program : Program) : Context Unit :=
  {program:=program,foreign:=fun primitive args before result after=>match primitive with
    | .call operation=>∃value,result=.value value ∧ PlatformMemory.Call Unit operation args before value after
    | _=>False,
   headerConstant:=fun _=>none,builtin:=fun _ _=>none}

theorem memoryContext_hasMemory (program : Program) : HasMemory (memoryContext program) := by
  intro operation args before value after actual
  exact ⟨value,rfl,actual⟩

theorem memoryContext_sound (program : Program) : MemorySound (memoryContext program) := by
  intro operation args before result after _ actual
  exact actual

theorem call_external_of_absent {F : Type} {context : Context F} {cname : String}
    {args : List Value} {before after : State F} {result : CallResult}
    (absent : findFunction context.program cname=none) (run : Call context cname args before result after) :
    ∃operation,operation.name=cname ∧ context.foreign (.call operation) args before result after := by
  cases run with
  | external _ named actual=>exact ⟨_,named,actual⟩
  | internal selected _ _ _ _ _=>rw [absent] at selected;cases selected
  | internalVoid selected _ _ _ _ _=>rw [absent] at selected;cases selected
  | internalTerminated selected _ _ _=>rw [absent] at selected;cases selected

theorem size_argument_exact (n : Nat) (fit : n<2^64) :
    PlatformMemory.sizeArgument (.integer (integer64 n))=some n := by
  dsimp only [PlatformMemory.sizeArgument]
  rw [integer64_toInt,cast64_exact n fit]
  rfl

/-- EVERY permitted calloc call either fails with NULL and no new object, or
returns the actual fresh byte allocation. In particular the exact generic
contract excludes arbitrary successful application contents or return values. -/
theorem calloc_call_cases {F : Type} {context : Context F} {before after : State F}
    {length : Nat} {result : CallResult}
    (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (fit : length<2^64)
    (run : Call context "calloc" [.integer (integer64 length),.integer (integer64 8)] before result after) :
    (result=.value .null ∧ after=before) ∨
    (∃pointer,result=.value (.pointer pointer) ∧
      before.allocate .host (8*length) (PlatformMemory.zeroBytes (8*length))=some (pointer,after)) := by
  obtain ⟨operation,named,actual⟩:=call_external_of_absent absent run
  have eq : operation=.calloc := by cases operation <;> simp_all [External.name]
  subst operation
  obtain ⟨value,rfl,api⟩:=sound _ _ _ _ _ (Or.inl rfl) actual
  have countExpected:=size_argument_exact length fit
  have widthExpected:=size_argument_exact 8 (by norm_num)
  cases api with
  | callocFailure=>exact Or.inl ⟨rfl,rfl⟩
  | callocSuccess _ _ elements bytes _ _ pointer countSize widthSize noOverflow born=>
    have ce : elements=length:=Option.some.inj (countSize.symm.trans countExpected)
    have we : bytes=8:=Option.some.inj (widthSize.symm.trans widthExpected)
    subst elements
    subst bytes
    exact Or.inr ⟨pointer,rfl,by simpa only [Nat.mul_comm] using born⟩

/-- EVERY free call is either free(NULL), or the precise live host-object
release. This is a generic API fact, not an application result assumption. -/
theorem free_call_cases {F : Type} {context : Context F} {before after : State F}
    {argument : Value} {result : CallResult}
    (absent : findFunction context.program "free"=none) (sound : MemorySound context)
    (run : Call context "free" [argument] before result after) :
    result=.value .unit ∧ ((argument=.null ∧ after=before) ∨
      ∃pointer,argument=.pointer pointer ∧ PlatformMemory.release before pointer=some after) := by
  obtain ⟨operation,named,actual⟩:=call_external_of_absent absent run
  have eq : operation=.free := by cases operation <;> simp_all [External.name]
  subst operation
  obtain ⟨value,rfl,api⟩:=sound _ _ _ _ _ (Or.inr rfl) actual
  cases api with
  | freeNull=>exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
  | freeObject _ _ pointer released=>exact ⟨rfl,Or.inr ⟨pointer,rfl,released⟩⟩

#print axioms memoryContext_hasMemory
#print axioms memoryContext_sound
#print axioms calloc_call_cases
#print axioms free_call_cases
end RH080Next.FFTPV.MainAllocation
