/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadScale
import ExplicitFFTQuadIntegerModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

def stage (p : Profile) : List Stmt:=if p=.fap then [loop p,fapScaleStatement] else [loop p]
def stageStart : Profile → Nat | .fap=>34 | .w4=>35

theorem actual_stage (p : Profile) : ((ProductRow.items p.mainFunction.body).drop (stageStart p)).take (stage p).length=stage p:=by
  cases p <;> rfl

/-- A source segment contract. The real main caller must establish typed arrays,
its actual borrowed locals with j=0/status=0, and zero quad magnitude. No completed
quadrature or numerical value is assumed. Complete main/ANT consumption is separate. -/
def Correct {F : Type} (context : Context F) (before : State F) (input : InputLoader.Input) (workObject fo : Nat)
    (paramIds : Parameter → Nat) (auxIds : Aux → Nat) (dataMemory oldWork : Nat → Nat) : Prop:=
  ∃after memory,ExecList context before (stage input.profile) .normal after ∧ EveryList context before (stage input.profile) .normal after ∧
    WordArrayRep after input.object (12*input.profile.grid) dataMemory ∧ WordArrayRep after workObject 512 memory ∧
    Locals after parameterName parameterType paramIds fo (parameterValues input input.profile.count) ∧
    Locals after auxName auxType auxIds fo (auxValues workObject) ∧
    MultiplyCall.CallerFrame before after [workObject,paramIds .j] ∧
    (∀k<6,memory (208+k)< base) ∧ FFT.Limbs.magnitude base 6 (fun k=> memory (208+k))=scaledModel input.profile ∧
    ∀k,(k<160 ∨ 166≤ k) → (k<208 ∨ 214≤ k) → memory k=oldWork k

theorem quad_stage_total {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo 0 paramIds auxIds dataMemory workData) (pinned : context.program=input.profile.program) :
    Correct context before input workObject fo paramIds auxIds dataMemory workData:=by
  obtain ⟨middle,rawMemory,loopRun,loopEvery,post,loopFrame,loopEnv,loopScope,loopOutside⟩:=
    loop_execution context input.profile.count h pinned (by omega) (le_refl _)
  by_cases fap : input.profile=.fap
  · obtain ⟨after,memory,scaleRun,scaleEvery,data,array,parameters,aux,scaleFrame,digits,value,outside⟩:=fap_scale_execution context post pinned
    have frame : ApplicationBirthFrame.Frame before.nextObject before after [workObject,paramIds .j]:=
      loopFrame.trans (frame_widen (lower_frame scaleFrame.frame loopFrame.fresh) (by simp))
    refine ⟨after,memory,?_,?_,data,array,parameters,aux,⟨scaleFrame.environment.trans loopEnv,scaleFrame.scope.trans loopScope,frame⟩,digits,?_,?_⟩
    · simpa only [stage,if_pos fap] using ExecList.cons loopRun (.cons scaleRun .nil)
    · simpa only [stage,if_pos fap] using every_cons loopEvery (every_cons scaleEvery (every_nil after))
    · exact value.trans (by rw [raw_quad_model];simp only [scaledModel,if_pos fap])
    · intro k ht hq;exact (outside k hq).trans (loopOutside k ht hq)
  · refine ⟨middle,rawMemory,?_,?_,post.array,post.work,post.parameters,post.aux,⟨loopEnv,loopScope,loopFrame⟩,post.quadDigits,?_,loopOutside⟩
    · simpa only [stage,if_neg fap] using ExecList.cons loopRun .nil
    · simpa only [stage,if_neg fap] using every_cons loopEvery (every_nil middle)
    · exact post.quadValue.trans (by rw [raw_quad_model];simp only [scaledModel,if_neg fap])

theorem source_quad_stage_total {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo 0 paramIds auxIds dataMemory workData) (pinned : context.program=input.profile.program) :
    Correspondence.SourceSyntaxCorresponds input.profile.source input.profile.program ∧
      ((ProductRow.items input.profile.mainFunction.body).drop (stageStart input.profile)).take (stage input.profile).length=stage input.profile ∧
      Correct context before input workObject fo paramIds auxIds dataMemory workData:=
  ⟨input.profile.actual_syntax,actual_stage input.profile,quad_stage_total context h pinned⟩

#print axioms quad_stage_total
#print axioms source_quad_stage_total
end RH080Next.FFTPV.QuadSource
