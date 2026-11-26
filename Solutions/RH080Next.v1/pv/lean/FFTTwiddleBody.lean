/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleAdvance
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

private theorem two_unique {F : Type} {context : Context F} {before middle after other : State F}
    {a b : Stmt} {flow : Flow}
    (first : ∀state flow,Exec context before a flow state → flow=.normal ∧ state=middle)
    (second : ∀state flow,Exec context middle b flow state → flow=.normal ∧ state=after)
    (run : ExecList context before [a,b] flow other) : flow=.normal ∧ other=after := by
  cases run with
  | abrupt run abrupt=>exact False.elim (abrupt (first _ _ run).1)
  | cons run rest=>
    obtain ⟨_,same⟩:=first _ _ run
    cases same
    cases rest with
    | abrupt run abrupt=>exact False.elim (abrupt (second _ _ run).1)
    | cons run rest=>
      obtain ⟨_,same⟩:=second _ _ run
      cases same
      cases rest
      exact ⟨rfl,rfl⟩

/-- Complete actual loop block, including both statement executions, all
scope exits, source-written table words and the preserved actual root. -/
theorem body_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {tableObject workObject n owner j : Nat}
    {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View before tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2) :
    ∃after nextTable nextWork,Exec context before loopBody .normal after ∧
      View after tableObject workObject n ids owner (j+1) nextTable nextWork seed ∧
      Frame before.nextObject before after [tableObject,workObject,ids Var.j] ∧
      (∀k,k<512 →46≤k → nextWork k=workData k) ∧
      (∀k,k<n/2*12 → (k<j*12 ∨ j*12+12≤k) → nextTable k=tableData k) ∧
      (∀other flow,Exec context before loopBody flow other → flow=.normal ∧ other=after) := by
  obtain ⟨middle,nextTable,nextWork,callRun,hm,newValue,newDigits,newSigns,callFrame,outWork,outTable,everyCall⟩:=
    call_execution context functions h.enter inside
  obtain ⟨last,inc,hl,incFrame⟩:=advance_execution context hm inside newValue newDigits newSigns
  have incOnly : SourceNoAlloc.Only advance := by simp [advance,SourceNoAlloc.Only,SourcePure.CallFree]
  have incEffect := SourceNoAlloc.exec_effect inc incOnly hm.well
  have enlarged : Frame before.nextObject before.enterScope middle [tableObject,workObject,ids Var.j] := by
    refine ⟨callFrame.frame.well,callFrame.frame.fresh,callFrame.frame.nextObject,callFrame.frame.nextScope,
      callFrame.frame.mode,callFrame.frame.foreign,?_⟩
    intro id old away
    exact callFrame.frame.outside id old (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away ⊢;exact ⟨away.1,away.2.1⟩)
  have tailFrame : Frame before.nextObject middle last [tableObject,workObject,ids Var.j] := by
    refine ⟨incEffect.well,?_,?_,incFrame.nextScope,incFrame.mode,incEffect.foreign,?_⟩
    · rw [incFrame.nextObject];exact enlarged.fresh
    · rw [incFrame.nextObject]
    · intro id old away
      exact incFrame.outside id (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.2.2)
  have closed := close_frame h.well (le_refl before.nextObject) (enlarged.trans tailFrame)
  let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
  have runList : ExecList context before.enterScope [callStmt,advance] .normal last := .cons callRun (.cons inc .nil)
  have run : Exec context before loopBody .normal after := .block (by rfl) runList (by rfl)
  have post : View after tableObject workObject n ids owner (j+1) nextTable nextWork seed := by
    refine ⟨hl.locals.leave (by have bound:=h.locals.bound;omega) before.environment h.locals.lookup before.scope,
      ComplexSource.word_array_leave hl.table before.nextScope before.scope before.environment,
      ComplexSource.word_array_leave hl.work before.nextScope before.scope before.environment,
      hl.different,hl.separate,hl.nbound,hl.active,hl.tableDigits,hl.tableSigns,hl.tableValues,
      hl.rootDigits,hl.rootSigns,hl.rootValue,hl.rootSmall,hl.valuesSmall,closed.well⟩
  refine ⟨after,nextTable,nextWork,run,post,closed,outWork,outTable,?_⟩
  intro other flow arbitrary
  cases arbitrary with
  | block entered arbitrary finish=>
    subst_vars
    have second : ∀state flow,Exec context middle advance flow state → flow=.normal ∧ state=last := by
      intro state flow exec
      obtain ⟨eqf,eqs⟩:=PureDeterminism.simple_unique (by simp [advance,PureDeterminism.Simple,SourcePure.CallFree]) inc exec
      exact ⟨eqf.symm,eqs.symm⟩
    obtain ⟨eqf,eqs⟩:=two_unique everyCall second arbitrary
    exact ⟨eqf,by rw [eqs];rfl⟩

#print axioms body_execution
end RH080Next.FFTPV.TwiddleSource
