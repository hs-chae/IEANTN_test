/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleBody
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

private theorem false_loop_every {F : Type} {context : Context F} {before other : State F} {flow : Flow}
    (ev : Eval context before condition (.integer (.boolean false)) before)
    (run : Exec context before loop flow other) : flow=.normal ∧ other=before := by
  cases run <;> (obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [condition,SourcePure.CallFree]) ev (by assumption))
  · exact ⟨rfl,rfl⟩
  all_goals simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed] at *

private theorem true_loop_every {F : Type} {context : Context F} {before middle after other : State F} {flow : Flow}
    (ev : Eval context before condition (.integer (.boolean true)) before)
    (bodyEvery : ∀state flow,Exec context before loopBody flow state → flow=.normal ∧ state=middle)
    (restEvery : ∀state flow,Exec context middle loop flow state → flow=.normal ∧ state=after)
    (run : Exec context before loop flow other) : flow=.normal ∧ other=after := by
  cases run <;> (obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [condition,SourcePure.CallFree]) ev (by assumption))
  · simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed] at *
  · obtain ⟨_,rfl⟩:=bodyEvery _ _ (by assumption)
    exact restEvery _ _ (by assumption)
  · have bad:= (bodyEvery _ _ (by assumption)).1
    cases bad
  · have bad:= (bodyEvery _ _ (by assumption)).1
    cases bad
  · have bad:= (bodyEvery _ _ (by assumption)).1
    simp_all

/-- Every actual iteration of the preserved C table constructor is proved.
The table's entire prefix refines the exact integer multiplication recurrence;
no table-value, successful-execution or observed-output premise is supplied. -/
theorem loop_execution {F : Type} (context : Context F) (functions : Functions context) (steps : Nat)
    {before : State F} {tableObject workObject n owner j : Nat}
    {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View before tableObject workObject n ids owner j tableData workData seed) (remaining : j+steps=n/2) :
    ∃after nextTable nextWork,Exec context before loop .normal after ∧
      View after tableObject workObject n ids owner (n/2) nextTable nextWork seed ∧
      Frame before.nextObject before after [tableObject,workObject,ids Var.j] ∧
      (∀k,k<512 →46≤k → nextWork k=workData k) ∧
      (∀other flow,Exec context before loop flow other → flow=.normal ∧ other=after) := by
  induction steps generalizing before j tableData workData with
  | zero=>
    have jj : j=n/2 := by omega
    subst j
    have ev : Eval context before condition (.integer (.boolean false)) before := by simpa using condition_eval context h
    refine ⟨before,tableData,workData,.whileFalse ev (by rfl),h,Frame.refl before.nextObject _ h.well (le_refl _),fun _ _ _=>rfl,?_⟩
    intro other flow run
    exact false_loop_every ev run
  | succ steps ih=>
    have inside : j<n/2 := by omega
    obtain ⟨middle,middleTable,middleWork,first,hm,firstFrame,outWork,outTable,firstEvery⟩:=body_execution context functions h inside
    obtain ⟨after,nextTable,nextWork,rest,ha,restFrame,lastWork,restEvery⟩:=ih hm (by omega)
    have restricted : Frame before.nextObject middle after [tableObject,workObject,ids Var.j] := by
      refine ⟨restFrame.well,firstFrame.fresh.trans restFrame.nextObject,restFrame.nextObject,restFrame.nextScope,
        restFrame.mode,restFrame.foreign,?_⟩
      intro id old away
      exact restFrame.outside id (lt_of_lt_of_le old firstFrame.nextObject) away
    have ev : Eval context before condition (.integer (.boolean true)) before := by simpa only [inside,decide_true] using condition_eval context h
    refine ⟨after,nextTable,nextWork,.whileNext ev (by rfl) first rest,ha,firstFrame.trans restricted,?_,?_⟩
    · intro k hk outside
      exact (lastWork k hk outside).trans (outWork k hk outside)
    · intro other flow run
      exact true_loop_every ev firstEvery restEvery run

#print axioms loop_execution
end RH080Next.FFTPV.TwiddleSource
