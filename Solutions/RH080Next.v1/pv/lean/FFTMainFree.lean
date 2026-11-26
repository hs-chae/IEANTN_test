/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainCounters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Generic release preserves all actual lexical slots and caller clocks
outside the one released host object. It assumes no program answer. -/
theorem release_caller_frame {F : Type} {before after : State F} {pointer : Pointer}
    (well : WellScoped before) (released : PlatformMemory.release before pointer=some after) :
    MultiplyCall.CallerFrame before after [pointer.object] := by
  unfold PlatformMemory.release at released
  cases present : before.objects pointer.object with
  | none=>simp [present] at released
  | some object=>
    simp only [present] at released
    split_ifs at released
    cases Option.some.inj released
    have wa : WellScoped {before with objects:=fun id=>if id=pointer.object then some ({object with live:=false} : Object) else before.objects id} := by
      refine ⟨well.current,?_,?_⟩
      · intro id obj observed
        by_cases same : id=pointer.object
        · subst id
          simp only [ite_true,Option.some.injEq] at observed
          cases observed
          exact well.objectIds _ _ present
        · exact well.objectIds _ _ (by simpa [same] using observed)
      · intro id obj owner observed automatic
        by_cases same : id=pointer.object
        · subst id
          simp only [ite_true,Option.some.injEq] at observed
          cases observed
          exact well.automatic _ _ owner present automatic
        · exact well.automatic _ _ owner (by simpa [same] using observed) automatic
    refine ⟨rfl,rfl,wa,le_refl _,le_refl _,le_refl _,rfl,rfl,?_⟩
    intro id old absent
    have ne : id≠pointer.object := by simpa using absent
    simp [ne]

/-- EVERY actual free call on a pointer has precisely the generic release
frame, under the exact generic allocator/deallocator contract. -/
theorem free_call_framed {F : Type} {context : Context F} {before after : State F}
    {pointer : Pointer} {result : CallResult}
    (absent : findFunction context.program "free"=none) (sound : MemorySound context)
    (well : WellScoped before) (run : Call context "free" [.pointer pointer] before result after) :
    result=.value .unit ∧ MultiplyCall.CallerFrame before after [pointer.object] := by
  obtain ⟨value,cases⟩:=free_call_cases absent sound run
  refine ⟨value,?_⟩
  rcases cases with ⟨impossible,_⟩ | ⟨p,same,released⟩
  · cases impossible
  · cases Value.pointer.inj same
    exact release_caller_frame well released

/-- Existence of the actual free Call follows from a live host allocation;
its frame and EVERY allowed Call follow from the precise API semantics. -/
theorem free_words_total {F : Type} (context : Context F) {before : State F}
    (object length : Nat) (data : Nat → Nat)
    (absent : findFunction context.program "free"=none) (has : HasMemory context) (sound : MemorySound context)
    (well : WellScoped before) (rep : WordArrayRep before object length data) :
    ∃after,Call context "free" [.pointer (wordPointer object 0)] before (.value .unit) after ∧
      MultiplyCall.CallerFrame before after [object] ∧
      (∀other result,Call context "free" [.pointer (wordPointer object 0)] before result other →
        result=.value .unit ∧ other=after) := by
  let after : State F:={before with objects:=fun id=>if id=object then some ({wordObject length data with live:=false} : Object) else before.objects id}
  have released : PlatformMemory.release before (wordPointer object 0)=some after := by
    simp [PlatformMemory.release,wordPointer,rep.2.1,wordObject,after]
  have called : Call context "free" [.pointer (wordPointer object 0)] before (.value .unit) after :=
    .external absent rfl (has _ _ _ _ _ (.freeObject _ _ _ released))
  refine ⟨after,called,release_caller_frame well released,?_⟩
  intro other result actual
  obtain ⟨value,outcome⟩:=free_call_cases absent sound actual
  refine ⟨value,?_⟩
  rcases outcome with ⟨impossible,_⟩ | ⟨p,same,run⟩
  · cases impossible
  · cases Value.pointer.inj same
    exact Option.some.inj (run.symm.trans released)

#print axioms release_caller_frame
#print axioms free_call_framed
#print axioms free_words_total
end RH080Next.FFTPV.MainAllocation
