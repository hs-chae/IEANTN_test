/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFinishBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainFinish
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource
open MainRootBirth

def answerAndFreeStatements (fap : Bool) : List Stmt :=
  [AnswerSource.answerDeclaration,AnswerSource.statusBranch (AnswerSource.profileAllowance fap)]++
    MainAllocation.normFinalStatements fap

/-- Real answer declaration, both guarded conversions, all four source frees,
and the actual return. Every possible finite execution has the same computed
sentinel-aware answer. All buffers/slots are the actual incoming application
objects, not trusted initialization or successful-effect hypotheses. -/
theorem answer_and_free {F : Type} (context : Context F) (fap : Bool)
    (programPinned : context.program=AnswerSource.profileProgram fap)
    {before : State F} {n nId owner base status : Nat}
    {objects ids : MainAllocation.Role → Nat} {data : MainAllocation.Role → Nat → Nat}
    (locals : FullMainLocals before n nId owner objects ids base status)
    (well : WellScoped before) (scope : before.scope=owner)
    (different : Function.Injective objects)
    (arrays : ∀r,WordArrayRep before (objects r) (MainAllocation.length n r) (data r))
    (has : MainAllocation.HasMemory context) (sound : MainAllocation.MemorySound context)
    (totalDigits : ∀k,k<6 → data .work (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data .work (208+k)<1000000000) :
    ∃after,ReturningSegment context before (answerAndFreeStatements fap)
        (.integer (integer64 (AnswerSource.result (data .work) (AnswerSource.profileAllowance fap)))) after ∧
      after.scope=owner ∧
      Frame before.nextObject before after (MainAllocation.finalFreeOrder.map objects) ∧
      AnswerSource.result (data .work) (AnswerSource.profileAllowance fap)<2^64 := by
  have params : Locals before (fun v=>AnswerSource.name (AnswerSource.inputLift v))
      (fun v=>AnswerSource.type (AnswerSource.inputLift v)) (answerIds nId ids base status)
      before.scope (fun v=>AnswerSource.values (objects .work) 0 0 0 (AnswerSource.inputLift v)) := by
    rw [scope]
    exact answer_locals locals
  have work : WordArrayRep before (objects .work) 512 (data .work):=arrays .work
  have separate : ∀v,objects .work≠answerIds nId ids base status v :=
    fun v=>MultiplyParameters.array_slot_different work (params.slots v)
  obtain ⟨_,_,_,answered,answerId,run,answerSlot,answerLookup,answerScope,rep,frame,fits,every⟩:=
    AnswerSource.source_answer_total context fap programPinned before (objects .work)
      (answerIds nId ids base status) (data .work) well params work separate totalDigits quadDigits
  have fullAfter : FullMainLocals answered n nId owner objects ids base status := by
    apply MainTransport.locals_of_frame well locals frame (answer_lookup run)
    intro v
    simp
  have allArrays : ∀r,WordArrayRep answered (objects r) (MainAllocation.length n r) (data r) := by
    intro r
    exact MainTransport.array_of_frame well (arrays r) frame (by simp)
  have freeView : MainAllocation.FreeView answered n objects ids (fun _=>owner) data
      answerId before.scope (AnswerSource.result (data .work) (AnswerSource.profileAllowance fap)) MainAllocation.finalFreeOrder := by
    refine ⟨?_,?_,fun r _=>allArrays r,different,answerLookup,answerSlot,frame.well⟩
    · intro r member
      exact fullAfter.lookup (some (.inl (some r)))
    · intro r member
      exact fullAfter.slots (some (.inl (some r)))
  have absent : findFunction context.program "free"=none := by
    rw [programPinned]
    cases fap <;> rfl
  obtain ⟨after,freeRun,freeEvery,env,freeScope,freeFrame⟩:=
    freeView.source_final_total context fap absent has sound
  have answerFrame : Frame before.nextObject before answered (MainAllocation.finalFreeOrder.map objects) :=
    frame_widen frame (by intro i member;cases member)
  have lastFrame : Frame before.nextObject answered after (MainAllocation.finalFreeOrder.map objects) :=
    MainAllocation.lower_cutoff freeFrame frame.nextObject
  exact ⟨after,then_return ⟨run,every⟩ ⟨freeRun,freeEvery⟩,
    freeScope.trans (answerScope.trans scope),answerFrame.trans lastFrame,fits⟩

#print axioms answer_and_free
end RH080Next.FFTPV.MainFinish
