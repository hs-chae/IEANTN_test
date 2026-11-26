/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadAdvance
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

/-- The complete seven-instruction actual quad row, including the real C
selector, three source helpers, real status assignments and scoped lifetimes. -/
theorem row_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo j : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo j paramIds auxIds dataMemory workData)
    (pinned : context.program=input.profile.program) (hj : j< input.profile.count) :
    ∃after memory,Exec context before loopBody .normal after ∧ Every context before loopBody .normal after ∧
      LoopView after input workObject fo (j+1) paramIds auxIds dataMemory memory ∧
      ApplicationBirthFrame.Frame before.nextObject before after [workObject,paramIds .j] ∧
      after.environment=before.environment ∧ after.scope=before.scope ∧
      ∀k,(k<160 ∨ 166≤ k) → (k<208 ∨ 214≤ k) → memory k=workData k:=by
  have entered:=h.enter_body hj
  obtain ⟨s1,ids,run1,every1,h1,f1,idsEq⟩:=entered.prefix_execution context pinned
  obtain ⟨s2,m2,run2,every2,h2,temp2,f2,outside2⟩:=h1.magnitude_execution context pinned
  obtain ⟨s3,m3,run3,every3,h3,temp3,f3,outside3⟩:=h2.multiply_execution context temp2 pinned
  obtain ⟨s4,m4,run4,every4,h4,f4,outside4⟩:=h3.add_execution context temp3 pinned
  obtain ⟨finished,run5,every5,finalView,f5,env5,scope5⟩:=h4.advance_execution context
  have sameIds (p : Parameter) : ids (.inl p)=paramIds p:=idsEq p
  have idFun : (fun p=> ids (.inl p))=paramIds:=funext sameIds
  rw [idFun] at finalView
  rw [sameIds .j] at f5
  have bodyRun : ExecList context before.enterScope rowStatements .normal finished:=
    append_normal run1 (.cons run2 (.cons run3 (.cons run4 (.cons run5 .nil))))
  have bodyEvery : EveryList context before.enterScope rowStatements .normal finished:=
    every_append every1 (every_cons every2 (every_cons every3 (every_cons every4 (every_cons every5 (every_nil finished)))))
  have padEmpty {a b : State F} (frame : ApplicationBirthFrame.Frame before.nextObject a b []) :
      ApplicationBirthFrame.Frame before.nextObject a b [workObject,paramIds .j]:=frame_widen frame (by intros;simp_all)
  have padWork {a b : State F} (frame : ApplicationBirthFrame.Frame before.nextObject a b [workObject]) :
      ApplicationBirthFrame.Frame before.nextObject a b [workObject,paramIds .j]:=frame_widen frame (by simp)
  have whole:=(padEmpty f1).trans ((padWork f2).trans ((padWork f3).trans ((padWork f4).trans f5)))
  let after : State F:={finished.leaveScope before.nextScope before.environment with scope:=before.scope}
  have frame:=ApplicationBirthFrame.close_frame h.well (le_refl _) whole
  have different : before.nextScope≠fo:=by have bound:=h.parameters.bound;omega
  have parameters:=finalView.parameters.leave different before.environment h.parameters.lookup before.scope
  have aux:=finalView.aux.leave different before.environment h.aux.lookup before.scope
  have final : LoopView after input workObject fo (j+1) paramIds auxIds dataMemory m4:=
    ⟨parameters,aux,IncrementSource.wordArray_leave finalView.array,IncrementSource.wordArray_leave finalView.work,
      h.different,h.dataSeparate,h.workSeparate,h.auxSeparate,h.cross,finalView.active,finalView.quadDigits,finalView.quadValue,frame.well⟩
  exact ⟨after,m4,.block (by rfl) bodyRun (by rfl),every_block bodyEvery,final,frame,rfl,rfl,
    fun k ht hq=>(outside4 k hq).trans ((outside3 k ht).trans (outside2 k ht))⟩

#print axioms row_execution
end RH080Next.FFTPV.QuadSource
