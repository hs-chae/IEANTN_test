/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumAdvance
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
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

/-- The actual source sum block executes the proved unsigned accumulator,
advances its real counter, preserves all output samples and every workspace
word outside total192..197, and restores the real loop scope. -/
theorem body_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "add_magnitude"=some add_magnitude_ast)
    {before : State F} {outputObject workObject n owner i : Nat}
    {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View before outputObject workObject n ids owner i outputData workData samples) (inside : i<n) :
    ∃after nextWork,Exec context before loopBody .normal after ∧
      View after outputObject workObject n ids owner (i+1) outputData nextWork samples ∧
      Frame before.nextObject before after [workObject,ids Var.i] ∧
      (∀k,(k<192 ∨ 198≤k) → nextWork k=workData k) ∧
      (∀other flow,Exec context before loopBody flow other → flow=.normal ∧ other=after) := by
  obtain ⟨middle,nextWork,callRun,hm,callFrame,outWork,everyCall⟩:=call_execution context selected h.enter inside
  obtain ⟨last,inc,hl,incFrame⟩:=advance_execution context hm inside
  have incOnly : SourceNoAlloc.Only advance:=by simp [advance,SourceNoAlloc.Only,SourcePure.CallFree]
  have incEffect:=SourceNoAlloc.exec_effect inc incOnly hm.well
  have enlarged : Frame before.nextObject before.enterScope middle [workObject,ids Var.i] := by
    refine ⟨callFrame.frame.well,callFrame.frame.fresh,callFrame.frame.nextObject,callFrame.frame.nextScope,
      callFrame.frame.mode,callFrame.frame.foreign,?_⟩
    intro id old away
    exact callFrame.frame.outside id old (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.1)
  have tailFrame : Frame before.nextObject middle last [workObject,ids Var.i] := by
    refine ⟨incEffect.well,?_,?_,incFrame.nextScope,incFrame.mode,incEffect.foreign,?_⟩
    · rw [incFrame.nextObject];exact enlarged.fresh
    · rw [incFrame.nextObject]
    · intro id old away
      exact incFrame.outside id (by simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at away;simp only [List.mem_singleton];exact away.2)
  have closed:=close_frame h.well (le_refl before.nextObject) (enlarged.trans tailFrame)
  let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
  have runList : ExecList context before.enterScope [callStmt,advance] .normal last:=.cons callRun (.cons inc .nil)
  have run : Exec context before loopBody .normal after:=.block (by rfl) runList (by rfl)
  have post : View after outputObject workObject n ids owner (i+1) outputData nextWork samples := by
    refine ⟨hl.locals.leave (by have bound:=h.locals.bound;omega) before.environment h.locals.lookup before.scope,
      ComplexSource.word_array_leave hl.output before.nextScope before.scope before.environment,
      ComplexSource.word_array_leave hl.work before.nextScope before.scope before.environment,
      hl.different,hl.separate,hl.nbound,hl.active,hl.outputDigits,hl.outputValues,hl.outputSmall,
      hl.totalDigits,hl.totalValue,closed.well⟩
  refine ⟨after,nextWork,run,post,closed,outWork,?_⟩
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
end RH080Next.FFTPV.OutputSumSource
