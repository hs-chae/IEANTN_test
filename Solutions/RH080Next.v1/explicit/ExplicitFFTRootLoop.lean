/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootBody
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

/-- Closing the actual loop-body block retains the enclosing function-owned
pointer, status and i slots. Its fresh temporary scope is really freed. -/
theorem Runtime.close_block {F : Type} {before middle : State F} {input : Input}
    {owner statusId indexId oldIndex newIndex : Nat} {ids : Param → Nat} {old data : Nat → Nat}
    (initial : Runtime before input owner statusId indexId ids old oldIndex)
    (last : Runtime middle input owner statusId indexId ids data newIndex)
    (body : ApplicationBirthFrame.Frame (ids .root) before.enterScope middle [input.layout.object]) :
    Runtime {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      input owner statusId indexId ids data newIndex := by
  have rootBound:=initial.view.params.well.objectIds _ _ (initial.view.params.locals.slots Param.root).object
  have full:=ApplicationBirthFrame.close_frame initial.view.params.well rootBound.le body
  have different : before.nextScope≠owner:=by have hb:=initial.view.params.locals.bound;omega
  have locals:=last.view.params.locals.leave different before.environment initial.view.params.locals.lookup before.scope
  have status : Slot {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      statusId owner .u64 (.integer (integer64 0)):=by
    refine ⟨last.view.status.storable,?_⟩
    change (middle.objects statusId).map _=_
    rw [last.view.status.object];simp [scalarObject,different.symm]
  have counter : Slot {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      indexId owner .u64 (.integer (integer64 newIndex)):=by
    refine ⟨last.counter.storable,?_⟩
    change (middle.objects indexId).map _=_
    rw [last.counter.object];simp [scalarObject,different.symm]
  exact ⟨⟨⟨IncrementSource.wordArray_leave last.view.params.array,locals,last.view.params.separate,full.well⟩,
      status,initial.view.statusLookup,last.view.statusSeparate⟩,counter,initial.lookup,last.separate,last.statusDifferent,
    last.paramsDifferent,last.indexFresh,initial.active⟩

theorem loop_block_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner statusId indexId j : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : Runtime before input owner statusId indexId ids data (j+1))
    (tracked : Tracked input data (regionValue input.n j)) (grid : OriginalGrid input.n) (hj : j<10) :
    ∃after nextData,Exec context before (.block iterationStatements) .normal after ∧
      Every context before (.block iterationStatements) .normal after ∧
      Runtime after input owner statusId indexId ids nextData (j+1+1) ∧
      Tracked input nextData (regionValue input.n (j+1)) ∧
      ApplicationBirthFrame.Frame (ids .root) before after [input.layout.object] ∧ after.scope=before.scope ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart ∨ input.layout.workStart+80≤ k) →
        (k < input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → nextData k=data k := by
  obtain ⟨middle,nextData,run,bodyEvery,post,values,frame,scope,outside⟩:=iteration_execution context functions h.enter tracked grid hj
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have initialRoot:=h.view.params.well.objectIds _ _ (h.view.params.locals.slots Param.root).object
  exact ⟨after,nextData,.block (by rfl) run (by rfl),every_block bodyEvery,h.close_block post frame,values,
    ApplicationBirthFrame.close_frame h.view.params.well initialRoot.le frame,rfl,outside⟩

/-- The complete ten actual source iterations terminate for each original
fixed grid. This is actual C-AST execution, not a trace supplied as a premise. -/
theorem loop_execution {F : Type} (context : Context F) (functions : Functions context)
    (remaining : Nat) {before : State F} {input : Input} {owner statusId indexId j : Nat}
    {ids : Param → Nat} {data : Nat → Nat} (count : j+remaining=10)
    (h : Runtime before input owner statusId indexId ids data (j+1))
    (tracked : Tracked input data (regionValue input.n j)) (grid : OriginalGrid input.n) :
    ∃after nextData,Exec context before sourceLoop .normal after ∧
      Every context before sourceLoop .normal after ∧
      Runtime after input owner statusId indexId ids nextData 11 ∧ Tracked input nextData (regionValue input.n 10) ∧
      ApplicationBirthFrame.Frame (ids .root) before after [input.layout.object] ∧ after.scope=before.scope ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart ∨ input.layout.workStart+80≤ k) →
        (k < input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → nextData k=data k := by
  induction remaining generalizing before j data with
  | zero=>
    have final : j=10:=by omega
    subst j
    have rootBound:=h.view.params.well.objectIds _ _ (h.view.params.locals.slots Param.root).object
    refine ⟨before,data,.whileFalse (loop_condition_eval context h (by omega)) ?_,
      every_while_false loop_condition_pure (loop_condition_eval context h (by omega)) (by rfl),h,tracked,
      ApplicationBirthFrame.Frame.refl _ _ h.view.params.well rootBound.le,rfl,fun _ _ _ _=>rfl⟩
    rfl
  | succ remaining ih=>
    have hj : j<10:=by omega
    obtain ⟨middle,nextData,body,bodyEvery,post,values,first,scope1,outside1⟩:=loop_block_execution context functions h tracked grid hj
    obtain ⟨after,finalData,rest,restEvery,last,finalValues,second,scope2,outside2⟩:=ih (by omega) post values
    have test : (.integer (.boolean (decide (j<10))) : Value).truth=some true:=by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]
    refine ⟨after,finalData,.whileNext (loop_condition_eval context h (by omega)) test body rest,
      every_while_next loop_condition_pure (loop_condition_eval context h (by omega)) test bodyEvery restEvery,
      last,finalValues,first.trans second,scope2.trans scope1,fun k hk hw hr=>(outside2 k hk hw hr).trans (outside1 k hk hw hr)⟩

#print axioms Runtime.close_block
#print axioms loop_block_execution
#print axioms loop_execution
end RH080Next.FFTPV.RootSource
