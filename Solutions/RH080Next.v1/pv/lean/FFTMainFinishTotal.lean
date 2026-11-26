/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFinishQuad
import FFTMainFinishAnswer
import FFTMainFailureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainFinish
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource
open MainRootBirth

def finishStatements (fap : Bool) : List Stmt:=
  NormalizeSource.quadStatements++answerAndFreeStatements fap

theorem actual_finish_statements (fap : Bool) :
    (MainAllocation.bodyItems (MainAllocation.failureSourceFunction fap)).drop 36=finishStatements fap := by
  cases fap <;> rfl

/-- Complete actual source suffix 36..45: three upward divisions, guarded
conversion/answer computation, four releases, and return.  The answer is
derived from the incoming actual accumulators, including the error sentinel.
No observed numerical answer or initial application state is a premise. -/
theorem source_finish_total {F : Type} (context : Context F) (fap : Bool)
    (programPinned : context.program=NormalizeSource.profileProgram fap)
    {before : State F} {n nId owner base status : Nat}
    {objects ids : MainAllocation.Role → Nat} {data : MainAllocation.Role → Nat → Nat}
    (locals : FullMainLocals before n nId owner objects ids base status)
    (well : WellScoped before) (scope : before.scope=owner)
    (different : Function.Injective objects)
    (arrays : ∀r,WordArrayRep before (objects r) (MainAllocation.length n r) (data r))
    (has : MainAllocation.HasMemory context) (sound : MainAllocation.MemorySound context)
    (positive : 0<n) (small : n<1000000000)
    (totalDigits : ∀k,k<6 → data .work (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data .work (208+k)<1000000000) :
    ∃after,ReturningSegment context before
        ((MainAllocation.bodyItems (MainAllocation.failureSourceFunction fap)).drop 36)
        (.integer (integer64 (finishValue fap n (magnitudeAt (data .work) 192) (magnitudeAt (data .work) 208)))) after ∧
      after.scope=owner ∧
      Frame before.nextObject before after (MainAllocation.finalFreeOrder.map objects) ∧
      finishValue fap n (magnitudeAt (data .work) 192) (magnitudeAt (data .work) 208)<2^64 := by
  obtain ⟨normalized,workData,quadRun,quadLocals,quadScope,quadArrays,quadFrame,totalValue,quadValue,totalNormalized,quadNormalized⟩:=
    normalized_quad context fap programPinned locals well scope different arrays positive small totalDigits quadDigits
  obtain ⟨after,answerRun,finalScope,answerFrame,fits⟩:=
    answer_and_free context fap programPinned quadLocals quadFrame.well quadScope different quadArrays has sound
      totalNormalized quadNormalized
  have valueEq : AnswerSource.result workData (AnswerSource.profileAllowance fap)=
      finishValue fap n (magnitudeAt (data .work) 192) (magnitudeAt (data .work) 208) := by
    rw [answer_result_eq workData fap totalNormalized quadNormalized,totalValue,quadValue]
    rfl
  have last : ReturningSegment context normalized (answerAndFreeStatements fap)
      (.integer (integer64 (finishValue fap n (magnitudeAt (data .work) 192) (magnitudeAt (data .work) 208)))) after := by
    simpa only [workUpdate,valueEq] using answerRun
  have firstFrame : Frame before.nextObject before normalized (MainAllocation.finalFreeOrder.map objects) := by
    apply frame_widen quadFrame
    intro i member
    obtain rfl:=List.mem_singleton.mp member
    simp [MainAllocation.finalFreeOrder]
  have lastFrame : Frame before.nextObject normalized after (MainAllocation.finalFreeOrder.map objects) :=
    MainAllocation.lower_cutoff answerFrame quadFrame.nextObject
  refine ⟨after,?_,finalScope,firstFrame.trans lastFrame,finishValue_fits fap n _ _⟩
  rw [actual_finish_statements]
  exact then_return quadRun last

theorem finishValue_of_small_sum (fap : Bool) (n total quad : Nat)
    (small : total+NormalizeSource.quadValue quad n+AnswerSource.profileAllowance fap<1000000000000000000) :
    finishValue fap n total quad=total+NormalizeSource.quadValue quad n+AnswerSource.profileAllowance fap := by
  have ht : total<1000000000000000000:=by omega
  have hq : NormalizeSource.quadValue quad n<1000000000000000000:=by omega
  unfold finishValue scalarConvert
  rw [if_pos ht,if_pos hq]
  unfold AnswerSource.computed
  rw [if_pos (by dsimp [AnswerSource.limit];omega),if_pos (by dsimp [AnswerSource.limit];omega)]

#print axioms actual_finish_statements
#print axioms source_finish_total
#print axioms finishValue_of_small_sum
end RH080Next.FFTPV.MainFinish
