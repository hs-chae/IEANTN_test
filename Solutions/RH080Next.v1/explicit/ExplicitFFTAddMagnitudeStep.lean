/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeTail
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem body_unique {F : Type} (context : Context F) : CompareSource.Unique context loopBody:=by
  apply CompareSource.block_unique
  intro stmt member
  simp only [bodyStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · exact fun a b=>PureDeterminism.simple_unique (by trivial) a b
  · exact x_branch_unique context
  · exact fun a b=>PureDeterminism.simple_unique (by trivial) a b
  · exact fun a b=>PureDeterminism.simple_unique (by trivial) a b
  · exact fun a b=>PureDeterminism.simple_unique (by trivial) a b
  · exact fun a b=>PureDeterminism.simple_unique (by trivial) a b

theorem loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop:=
  CompareSource.while_unique (by trivial) (body_unique context)

/-- The actual six source statements, with true nested x-if lifetime, t birth,
array store and both persistent updates. -/
theorem body_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner j : Nat} {li : Var → Nat}
    (h : View before input owner li j) (minId : ∀v,li .out≤li v) (hj : j< input.layout.n) :
    ∃after,ExecList context before bodyStatements .normal after ∧ View after input owner li (j+1) ∧
      ApplicationBirthFrame.Frame (li .out) before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  obtain ⟨s1,run1,h1,frame1,scope1⟩:=x_declare context h
  obtain ⟨s2,run2,every2,h2,frame2,scope2⟩:=x_branch_execution context h1 scope1.symm
  obtain ⟨s3,run3,h3,frame3,scope3⟩:=t_declare context h2 (scope2.trans scope1).symm hj
  obtain ⟨s4,run4,out4,a4,locals4,t4,lookup4,frame4,scope4⟩:=digit_execution context h3 hj
  obtain ⟨after,run56,post,frame56,scope56⟩:=counters_execution context out4 a4 locals4 h3.separate t4 lookup4 frame4.well minId hj
  have second : ApplicationBirthFrame.Frame before.nextObject s1 s2 [input.layout.outObject]:=by
    refine ⟨frame2.well,frame1.nextObject.trans frame2.fresh,frame2.nextObject,frame2.nextScope,frame2.mode,frame2.foreign,?_⟩
    intro id old absent
    exact frame2.outside id (lt_of_lt_of_le old frame1.nextObject) (by simp only [List.mem_singleton];omega)
  have first:=frame1.trans second
  have throughTemp:=first.trans (lower_frame frame3 first.nextObject)
  have throughDigit:=throughTemp.trans (lower_frame frame4 throughTemp.nextObject)
  have oldOut:=(h.well.objectIds _ _ (h.locals.slots Var.out).object).le
  exact ⟨after,.cons run1 (.cons run2 (.cons run3 (.cons run4 run56))),post,
    (lower_frame throughDigit oldOut).trans frame56,scope56.trans (scope4.trans (scope3.trans (scope2.trans scope1)))⟩

theorem block_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner j : Nat} {li : Var → Nat}
    (h : View before input owner li j) (minId : ∀v,li .out≤li v) (hj : j< input.layout.n) :
    ∃after,Exec context before loopBody .normal after ∧ View after input owner li (j+1) ∧
      ApplicationBirthFrame.Frame (li .out) before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  obtain ⟨middle,run,post,bodyFrame,scope⟩:=body_execution context h.enter minId hj
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have oldOut:=(h.well.objectIds _ _ (h.locals.slots Var.out).object).le
  have frame:=ApplicationBirthFrame.close_frame h.well oldOut bodyFrame
  have different : before.nextScope≠owner:=by have b:=h.locals.bound;omega
  obtain ⟨aData,aRep,aRead⟩:=post.inputArray
  exact ⟨after,.block (by rfl) run (by rfl),
    ⟨IncrementSource.wordArray_leave post.array,⟨_,IncrementSource.wordArray_leave aRep,aRead⟩,
      post.locals.leave different before.environment h.locals.lookup before.scope,post.separate,post.active,frame.well⟩,frame,rfl⟩

#print axioms body_unique
#print axioms body_execution
#print axioms block_execution
end RH080Next.FFTPV.AddMagnitudeSource
